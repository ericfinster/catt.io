(*****************************************************************************)
(*                                                                           *)
(*                        Internal Term Representation                       *)
(*                                                                           *)
(*****************************************************************************)

open Pd

open Cheshire.Monad
open Cheshire.Err
open Cheshire.Listmnd

open Printf

(*****************************************************************************)
(*                                   Terms                                   *)
(*****************************************************************************)
    
type ty_term =
  | ObjT
  | ArrT of ty_term * tm_term * tm_term
          
 and tm_term =
   | VarT of int
   | DefAppT of string * tm_term list
   | CohT of unit pd * ty_term * tm_term list 

let rec map_ty f ty =
  match ty with
  | ObjT -> ObjT
  | ArrT (typ,src,tgt) ->
    let typ' = map_ty f typ in 
    let src' = map_tm f src in 
    let tgt' = map_tm f tgt in 
    ArrT (typ',src',tgt')

and map_tm f tm =
  match tm with
  | VarT i -> VarT (f i)
  | DefAppT (id, args) ->
    let args' = List.map (map_tm f) args in
    DefAppT (id, args')
  | CohT (pd, typ, args) ->
    let args' = List.map (map_tm f) args in
    CohT (pd, typ, args')

let rec dim_typ typ =
  match typ with
  | ObjT -> 0
  | ArrT (typ',_,_) -> 1 + dim_typ typ'

(* Enclose the given pasting diagram of terms
 * with the boundaries specified by the given type *)
let rec suspend_with ty pd =
  match ty with
  | ObjT -> pd
  | ArrT (typ, src, tgt) ->
    suspend_with typ (Br (src,[(tgt,pd)]))

(* Return the term-labelled pasting diagram 
 * associated to a type/term pair *)
let disc_pd ty tm =
  suspend_with ty (Br (tm,[]))

(*****************************************************************************)
(*                             De Brujin Indices                             *)
(*****************************************************************************)

(* Extract de Brujin index from a list *)
let rec db_get i l =
  match l with
  | [] -> raise Not_found
  | x::xs ->
    if (i <= 0) then x
    else db_get (i-1) xs

(* De Brujin Lifting *)
let lift_tm tm k = map_tm ((+) k) tm
let lift_ty ty k = map_ty ((+) k) ty

(* Labels a given pasting diagram with 
 * its appropriate de Bruijn indices 
 *)
        
let rec to_db_run k pd =
  match pd with
  | Br (_,brs) ->
    let (brs', k') = to_db_brs k brs
    in (Br (VarT k', brs'), k'+1)
    
and to_db_brs k brs =
  match brs with
  | [] -> ([], k)
  | (_,b)::bs ->
    let (bs', k') = to_db_brs k bs in
    let (b' , k'') = to_db_run k' b in 
    ((VarT k'', b')::bs', k'' + 1)

let to_db pd = fst (to_db_run 0 pd)

(* Convert a pasting diagram (with de Bruijn labels) to a context.
 * This routine is not particularly efficient and could probably
 * stand to be improved.
*)
    
let rec pd_to_ctx_wtyp typ pd =
  match pd with
  | Br (s,brs) ->
    let lcl (t,b) = (pd_to_ctx_wtyp (ArrT (typ, s, t)) b) @ [typ] in
    let ll = List.map lcl brs in
    List.concat ll @ [typ]

let pd_to_ctx pd =
  pd_to_ctx_wtyp ObjT (to_db pd)

(*****************************************************************************)
(*                                Substitution                               *)
(*****************************************************************************)
        
let rec subst_ty sub ty =
  match ty with
  | ObjT -> ObjT
  | ArrT (typ, src, tgt) ->
     let typ' = subst_ty sub typ in
     let src' = subst_tm sub src in
     let tgt' = subst_tm sub tgt in
     ArrT (typ', src', tgt')

and subst_tm sub tm =
  match tm with
  | VarT i -> db_get i sub 
  | DefAppT (id, args) ->
     DefAppT (id, List.map (subst_tm sub) args)
  | CohT (pd, typ, args) ->
     CohT (pd, typ, List.map (subst_tm sub) args)

(*****************************************************************************)
(*                             Printing Raw Terms                            *)
(*****************************************************************************)
        
let rec print_ty_term t =
  match t with
  | ObjT -> "*"
  | ArrT (typ, src, tgt) -> 
     sprintf "%s | %s -> %s" (print_ty_term typ)
             (print_tm_term src) (print_tm_term tgt)
    
and print_tm_term t =
  match t with
  | VarT i -> sprintf "%d" i 
  | DefAppT (id, args) ->
    sprintf "%s(%s)" id (print_args args)
  | CohT (pd, typ, args) -> 
     sprintf "coh[%s : %s](%s)" (print_tm_pd pd) (print_ty_term typ) (print_args args)

and print_tm_pd _ = "unimplemented"
  
and print_args args =
  String.concat ", " (List.map print_tm_term args)

and print_decl (id, typ) =
  sprintf "(%s : %s)" id (print_ty_term typ) 

(*****************************************************************************)
(*                             Typechecking Monad                            *)
(*****************************************************************************)
              
type tc_def =
  | TCCellDef of unit pd * ty_term 
  | TCTermDef of ty_term list * ty_term * tm_term

type tc_env = {
    gma : ty_term list;
    rho : (string * tc_def) list;
  }

let empty_env = { gma = [] ; rho = [] }

type 'a tcm = tc_env -> 'a err

module TcMonad = MakeMonadError(struct

    type 'a t = 'a tcm
        
    let map f m env =
      match m env with
      | Ok a -> Ok (f a)
      | Fail s -> Fail s

    let pure a _ = Ok a
        
    let bind m f env =
      match m env with
      | Fail s -> Fail s
      | Ok a -> f a env

  end)(struct

    type e = string

    let throw s _ = Fail s
    let catch m h env =
      match m env with
      | Ok a -> Ok a
      | Fail s -> h s env
        
  end)

open TcMonad
open TcMonad.MonadSyntax

let tc_ok = pure
let tc_fail = throw

let tc_normalize tm = tc_ok tm
let tc_in_ctx g m env = m { env with gma = g }
let tc_ctx env = Ok env.gma
let tc_lift m _ = m

let err_lookup_var i l =
  try Ok (db_get i l)
  with Not_found -> Fail (sprintf "Unknown index: %d" i)
                      
let tc_lookup_var i env =
  err_lookup_var i env.gma

let tc_lookup_def id env =
  try Ok (List.assoc id env.rho)
  with Not_found -> Fail (sprintf "Unknown cell identifier: %s" id)

module LT = ListTraverse(TcMonad)
module PdT = PdTraverse(TcMonad)

(*****************************************************************************)
(*                                Typing Rules                               *)
(*****************************************************************************)

let rec tc_check_ty t = 
  match t with
  | ObjT -> tc_ok ObjT
  | ArrT (typ, src, tgt) ->
    let* typ' = tc_check_ty typ in
    let* src' = tc_check_tm src typ' in
    let* tgt' = tc_check_tm tgt typ' in
    tc_ok (ArrT (typ', src', tgt'))

and tc_check_tm tm ty =
  let* (tm', ty') = tc_infer_tm tm in
  let* ty_nf = tc_normalize ty in
  let* ty_nf' = tc_normalize ty' in

  let* _ = ensure (ty_nf = ty_nf') 
    (sprintf "The term %s was expected to have type %s,
                         but was inferred to have type %s"
       (print_tm_term tm') (print_ty_term ty) (print_ty_term ty')) in 

  tc_ok tm'
   
and tc_infer_tm tm =
  match tm with
  
  | VarT i ->
    let* typ = tc_lookup_var i in
    tc_ok (VarT i , typ)
      
  | DefAppT (id, _) -> (
    let* def = tc_lookup_def id in
    match def with
    | TCCellDef _ ->  tc_fail "unimplemented"
    | TCTermDef (_, _, _) -> tc_fail "unimplemented"
  )

  | CohT (pd, typ, sub) ->
    let pd_ctx = pd_to_ctx pd in
    let pd_db = to_db pd in 
    let pd_dim = dim_pd pd in 
    let* typ' = tc_in_ctx pd_ctx
        (let* rtyp = tc_check_ty typ in
         match rtyp with
         | ObjT -> tc_fail "No coherences have object type."
         | ArrT (btyp,src,tgt) -> 
           let* src_pd = tc_term_pd src in
           let* tgt_pd = tc_term_pd tgt in
           let typ_dim = dim_typ btyp in
           if (typ_dim >= pd_dim) then
             let* _ = ensure (src_pd = pd_db) ("Non-full source in coherence") in
             let* _ = ensure (tgt_pd = pd_db) ("Non-full target in coherence") in
             tc_ok rtyp
           else
             let pd_src = chop true (pd_dim - 1) pd_db in
             let pd_tgt = chop false (pd_dim - 1) pd_db in
             let* _ = ensure (src_pd = pd_src) ("Non-full source in composite") in
             let* _ = ensure (tgt_pd = pd_tgt) ("Non-full target in composite") in 
             tc_ok rtyp
        ) in
    (* Check the substitution and calculate the return type *)
    let* sub' = tc_check_sub sub in
    tc_ok (CohT (pd, typ', sub'), subst_ty sub' typ')

and tc_check_sub_rec sub ctx =
  match (sub, ctx) with 
  | (_::_, []) -> tc_fail "Too many arguments!"
  | ([], _::_) -> tc_fail "Not enough arguments!"
  | ([], []) -> tc_ok []
  | (tm::sub', typ::ctx') ->
    let* rsub = tc_check_sub_rec sub' ctx' in
    let typ' = subst_ty rsub typ in
    let* tm' = tc_check_tm tm typ' in
    tc_ok (tm'::rsub)

and tc_check_sub sub =
  let* ctx = tc_ctx in
  tc_check_sub_rec sub ctx
    
(* Extract the pasting diagram of a well typed term.
 * Note that the term is assumed to be well typed in 
 * the current context *)
      
and tc_term_pd tm =
  match tm with
  | VarT i -> 
    let* typ = tc_lookup_var i in
    tc_ok (disc_pd typ (VarT i))
  | DefAppT (_ , _) ->
    tc_fail "Not unfolding ..."
  | CohT (pd, _, sub) ->
    let* pd_sub = LT.traverse tc_term_pd sub in
    let m v = match v with
      | VarT i -> tc_lift (err_lookup_var i pd_sub)
      | _ -> tc_fail "Non-variable in pasting diagram" in 
    let* ppd = PdT.traverse m (to_db pd) in
    tc_ok (join_pd 0 ppd)
