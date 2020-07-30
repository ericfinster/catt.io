(*****************************************************************************)
(*                                                                           *)
(*                        Internal Term Representation                       *)
(*                                                                           *)
(*****************************************************************************)

open Pd

open Cheshire.Monad
open Cheshire.Err
(* open ErrMonad.MonadSyntax *)

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

(*****************************************************************************)
(*                             De Brujin Lifting                             *)
(*****************************************************************************)

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

let lift_tm tm k = map_tm ((+) k) tm
let lift_ty ty k = map_ty ((+) k) ty

(*****************************************************************************)
(*                                Substitution                               *)
(*****************************************************************************)

(* Extract de Brujin index from a list *)
(* Where does this belong ? *)
let rec get_var i l =
  match l with
  | [] -> raise Not_found
  | x::xs ->
    if (i <= 0) then x
    else get_var (i-1) xs
        
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
  | VarT i -> get_var i sub 
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

type 'a tcm = tc_env -> 'a err

module TcMonad : MonadError
  with type 'a t := 'a tcm
  with type e := string =
  MakeMonadError(struct

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
  
(*****************************************************************************)
(*                                Typing Rules                               *)
(*****************************************************************************)

let tc_normalize tm = tc_ok tm
let tc_in_ctx g m env = m { env with gma = g }
let tc_lift m _ = m
  
let tc_lookup_var i env =
  try Ok (get_var i env.gma)
  with Not_found -> Fail (sprintf "Unknown identfier: %d" i)

let tc_lookup_def id env =
  try Ok (List.assoc id env.rho)
  with Not_found -> Fail (sprintf "Unknown cell identifier: %s" id)
    
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
                        
  | CohT (_, _, _) -> tc_fail "cell check"

  (* match tm with
   * | VarT id -> 
   *    tc_lookup_var id >>= fun typ ->
   *    tc_ok (VarT id, typ)
   * | DefAppT (id, args) ->
   *    tc_lookup_def id >>= fun def ->
   *    (match def with
   *     | TCCellDef cell_tm -> 
   *        let pd = cell_pd cell_tm in
   *        tc_check_args args pd >>= fun sub ->
   *        let typ = subst_ty sub (cell_typ cell_tm) in 
   *        tc_ok (DefAppT (id, List.map snd sub), typ)
   *     | TCTermDef (tele, typ, _) -> 
   *        tc_check_args args tele >>= fun sub ->
   *        let typ' = subst_ty sub typ in
   *        tc_ok (DefAppT (id, List.map snd sub), typ')
   *    )
   * | CellAppT (cell, args) ->
   *    tc_check_cell cell >>= fun cell_tm ->
   *    let pd = cell_pd cell_tm in 
   *    tc_check_args args pd >>= fun sub ->
   *    let typ = subst_ty sub (cell_typ cell_tm) in 
   *    tc_ok (CellAppT (cell_tm, List.map snd sub), typ) *)
    
  (* match cell with
   * | CohT (pd, typ) -> 
   *    tc_check_pd pd >>= fun (pd', _, _) ->
   *    tc_with_vars pd' (tc_check_ty typ) >>= fun typ' ->
   *    let pd_vars = SS.of_list (List.map fst pd') in
   *    let typ_vars = ty_free_vars typ' in
   *    if (not (SS.subset pd_vars typ_vars)) then
   *      tc_fail "Coherence is not algebraic"
   *    else tc_ok (CohT (pd', typ'))
   * | CompT (_, ObjT) -> tc_fail "Composition cannot target an object"
   * | CompT (pd, ArrT (_, src, tgt)) ->
   *    tc_check_pd pd >>= fun (pd', _, _) ->
   *    tc_pd_src pd' >>= fun pd_src ->
   *    tc_pd_tgt pd' >>= fun pd_tgt ->
   *    tc_with_vars pd_src (tc_infer_tm src) >>= fun (src_tm, src_typ) ->
   *    tc_with_vars pd_tgt (tc_infer_tm tgt) >>= fun (tgt_tm, tgt_typ) ->
   *    tc_eq_nf_ty src_typ tgt_typ >>= fun nf_match -> 
   *    if (not nf_match) then
   *      tc_fail "Source and target do not have the same type"
   *    else let pd_src_vars = SS.of_list (List.map fst pd_src) in
   *         let pd_tgt_vars = SS.of_list (List.map fst pd_tgt) in
   *         let src_vars = SS.union (tm_free_vars src_tm) (ty_free_vars src_typ) in
   *         let tgt_vars = SS.union (tm_free_vars tgt_tm) (ty_free_vars tgt_typ) in
   *         if (not (SS.subset pd_src_vars src_vars)) then
   *           tc_fail "Source is not algebraic"
   *         else if (not (SS.subset pd_tgt_vars tgt_vars)) then
   *           tc_fail "Target is not algebraic"
   *         else tc_ok (CompT (pd', ArrT (src_typ, src_tm, tgt_tm))) *)

and tc_check_sub sub ctx =
  match (sub, ctx) with 
  | (_::_, []) -> tc_fail "Too many arguments!"
  | ([], _::_) -> tc_fail "Not enough arguments!"
  | ([], []) -> tc_ok []
  | (tm::sub', typ::ctx') ->
    let* rsub = tc_check_sub sub' ctx' in
    let typ' = subst_ty rsub typ in
    let* tm' = tc_check_tm tm typ' in
    tc_ok (tm'::rsub)


