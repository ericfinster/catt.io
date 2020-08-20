(*****************************************************************************)
(*                                                                           *)
(*                        Internal Term Representation                       *)
(*                                                                           *)
(*****************************************************************************)

open Pd
open Suite
    
open Cheshire.Err

(*****************************************************************************)
(*                                   Terms                                   *)
(*****************************************************************************)
    
type ty_term =
  | ObjT
  | ArrT of ty_term * tm_term * tm_term
          
 and tm_term =
   | VarT of int
   | DefAppT of string * tm_term suite
   | CohT of unit pd * ty_term * tm_term suite

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
    DefAppT (id, map (map_tm f) args)
  | CohT (pd, typ, args) ->
    CohT (pd, typ, map (map_tm f) args)

let rec dim_typ typ =
  match typ with
  | ObjT -> 0
  | ArrT (typ',_,_) -> 1 + dim_typ typ'

let rec nth_tgt n typ tm =
  if (n <= 0) then Ok (typ, tm) else
    match typ with
    | ObjT -> Fail "Target of object"
    | ArrT (typ',_,tgt) -> nth_tgt (n-1) typ' tgt

let rec nth_src n typ tm = 
  if (n <= 0) then Ok (typ, tm) else
    match typ with
    | ObjT -> Fail "Target of object"
    | ArrT (typ',src,_) -> nth_src (n-1) typ' src

(* Enclose the given pasting diagram of terms
 * with the boundaries specified by the given type *)
let rec suspend_with ty pd =
  match ty with
  | ObjT -> pd
  | ArrT (typ, src, tgt) ->
    suspend_with typ (Br (src, singleton (tgt,pd)))

(* Return the term-labelled pasting diagram 
 * associated to a type/term pair *)
let disc_pd ty tm =
  suspend_with ty (Br (tm, Emp))

(*****************************************************************************)
(*                             De Brujin Indices                             *)
(*****************************************************************************)

(* De Brujin Lifting *)
let lift_tm tm k = map_tm ((+) k) tm
let lift_ty ty k = map_ty ((+) k) ty

(* Labels a given pasting diagram with 
 * its appropriate de Bruijn indices 
 *)

(* Wait, this gets the indices wrong, right? *)
    
let rec to_db_run k pd =
  match pd with
  | Br (_,brs) ->
    let (k', brs') = to_db_brs k brs
    in (k'+1, Br (VarT k', brs'))
    
and to_db_brs k brs =
  match brs with
  | Emp -> (k,Emp)
  | Ext (bs,(_,b)) ->
    let (k', bs') = to_db_brs k bs in
    let (k'', b') = to_db_run k' b in 
    (k'' + 1, Ext (bs',(VarT k'', b')))

let to_db pd = snd (to_db_run 0 pd)

(* Convert a pasting diagram to a context. *)
let rec pd_to_ctx_br gma typ br =
  match br with
  | Br (_,brs) ->
    let gma' = Ext (gma, typ) in
    let typ' = lift_ty typ 1 in 
    pd_to_ctx_brs gma' (VarT 0) typ' brs 

and pd_to_ctx_brs gma src typ brs =
  match brs with
  | Emp -> (gma, src, typ)
  | Ext (brs',(_,br)) ->

    let (gma',src',typ') = pd_to_ctx_brs gma src typ brs' in

    let br_gma = Ext (gma', typ') in 
    let br_typ = ArrT (lift_ty typ' 1, lift_tm src' 1, VarT 0) in 
    
    let (gma'',_,typ'') = pd_to_ctx_br br_gma br_typ br in
    
    match typ'' with
    | ObjT -> raise Not_found
    | ArrT (bt,_,tgt) ->
      (gma'', tgt, bt)

let pd_to_ctx pd = pd_to_ctx_br Emp ObjT pd
      
(*****************************************************************************)
(*                             Printing Raw Terms                            *)
(*****************************************************************************)

open Format

let rec pp_print_ty ppf ty =
  match ty with
  | ObjT -> fprintf ppf "*"
  | ArrT (typ, src, tgt) ->
    fprintf ppf "%a | %a -> %a"
      pp_print_ty typ
      pp_print_tm src
      pp_print_tm tgt
              
and pp_print_tm ppf tm =
  match tm with
  | VarT i -> fprintf ppf "%d" i 
  | DefAppT (id, args) ->
    fprintf ppf "%s(%a)"
      id (pp_print_suite pp_print_tm) args
  | CohT (pd, typ, args) ->
    fprintf ppf "coh[%a : %a](%a)"
      (pp_print_pd (fun pf _ -> fprintf pf "()")) pd
      pp_print_ty typ
      (pp_print_suite pp_print_tm) args

let pp_print_ctx ppf gma =
  pp_print_suite pp_print_ty ppf gma

let print_tm = pp_print_tm std_formatter
let print_ty = pp_print_ty std_formatter

let print_ctx gma =
  fprintf std_formatter "@[<v>%a@]"
    pp_print_ctx gma 

    
    





