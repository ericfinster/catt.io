(*
 * typecheck.ml - catt typechecker
 *)

open Printf
open Common
open Syntax

module SS = Set.Make(String)

type tc_env = {
    gma : (string * ty_term) list;
    rho : (string * cell_term) list;
  }

let empty_env = { gma = [] ; rho = [] }
              
(* The typechecking monad *)
type 'a tcm = tc_env -> 'a err

(* Bind for the typechecking monad *)
let ( >>= ) m f env =
  match m env with
  | Fail s -> Fail s
  | Succeed a -> f a env
               
let tc_ok a _ = Succeed a
let tc_fail msg _ = Fail msg
let tc_in_ctx g m env = m { env with gma = g }
let tc_ctx env = Succeed env.gma
let tc_with_cell id cell m env = m { env with rho = (id, cell) :: env.rho }
let tc_with_var id ty m env = m { env with gma = (id, ty) :: env.gma }
let tc_with_vars vars m env = m { env with gma = vars @ env.gma }
let tc_ctx_vars env = Succeed (List.map fst env.gma)

(* Lookup and identifier in the context *)
let tc_lookup_var ident env =
  try Succeed (List.assoc ident env.gma)
  with Not_found -> Fail (sprintf "Unknown identifier: %s" ident)
    
(* Find the k-th target of the given term an type *)    
let rec tc_tgt_of a t k =
  if (k < 0) then
    tc_fail "Negative codimension"
  else if (k = 0) then
    tc_ok (a, t)
  else match t with
       | ObjT -> tc_fail "Object has no target"
       | ArrT (typ, _, tgt) -> tc_tgt_of tgt typ (k-1)

(* Source pasting diagram *)
let rec tc_pd_kth_src k pd =
  match pd with
  | [] -> tc_fail "Empty pasting diagram"
  | (id, ObjT) :: [] -> tc_ok ((id, ObjT) :: [])
  | (_, _) :: [] -> tc_fail "Malformed pasting diagram"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     if (dim_of tgt_typ >= k) then
       tc_pd_kth_src k pd'
     else
       tc_pd_kth_src k pd' >>= fun pd_src ->
       tc_ok ((fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd_src)

(* Target pasting diagram *)
let rec tc_pd_kth_tgt k pd =
  match pd with
  | [] -> tc_fail "Empty pasting diagram"
  | (id, ObjT) :: [] -> tc_ok ((id, ObjT) :: [])
  | (_, _) :: [] -> tc_fail "Malformed pasting diagram"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     let d = dim_of tgt_typ in
     if (d > k) then
       tc_pd_kth_tgt k pd'
     else tc_pd_kth_tgt k pd' >>= fun pd_tgt ->
          if (d = k) then
            match pd_tgt with
            | [] -> tc_fail "Empty pasting diagram target"
            | _ :: pd_tgt' -> tc_ok ((tgt_id, tgt_typ) :: pd_tgt')
          else tc_ok ((fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd_tgt)

let tc_pd_src pd = tc_pd_kth_src ((dim_of_pd pd) - 1) pd
let tc_pd_tgt pd = tc_pd_kth_tgt ((dim_of_pd pd) - 1) pd
                 
(* 
 * Typechecking Rules
 *)
    
let rec tc_check_ty t =
  match t with
  | ObjE -> tc_ok ObjT
  | ArrE (src, tgt) ->
     tc_infer_tm src >>= fun (src_tm, src_ty) ->
     tc_infer_tm tgt >>= fun (tgt_tm, tgt_ty) ->
     if (src_ty <> tgt_ty) then
       tc_fail "Ill-formed arrow type"
     else
       tc_ok (ArrT (src_ty, src_tm, tgt_tm))

and tc_check_tm x ty =
  tc_infer_tm x >>= fun (x_tm, x_ty) ->
  if (x_ty = ty) then tc_ok () else
    let msg = "Mismatch ..." in 
    (* let msg = sprintf "The term %s was expected to have type %s,  *)
    (*                    but was inferred to have type %s" *)
    (*                   (print_tm x) (print_ty t) (print_ty xt) in  *)
    tc_fail msg

and tc_infer_tm tm =
  match tm with
  | VarE id -> 
     tc_lookup_var id >>= fun typ ->
     tc_ok (VarT id, typ)
  | DefAppE (id, args) -> tc_fail "unimplemented"
  | CellAppE (cell, args) -> tc_fail "unimplemented"

and tc_check_cell cell =
  match cell with
  | CohE (pd, typ) -> 
     tc_check_pd pd >>= fun (pd', _, _) ->
     printf "Valid pasting diagram: %s\n" (print_term_ctx pd');
     tc_with_vars pd' (tc_check_ty typ) >>= fun typ' ->
     let pd_vars = SS.of_list (List.map fst pd') in
     let typ_vars = ty_free_vars typ' in
     if (not (SS.subset pd_vars typ_vars)) then
       tc_fail "Coherence is not algebraic"
     else tc_ok (CohT (pd', typ'))
  | CompE (pd, ObjE) -> tc_fail "Composition cannot target an object"
  | CompE (pd, ArrE (src, tgt)) ->
     tc_check_pd pd >>= fun (pd', _, _) ->
     printf "Valid pasting diagram: %s\n" (print_term_ctx pd');
     tc_pd_src pd' >>= fun pd_src ->
     printf "Source diagram: %s\n" (print_term_ctx pd_src);
     tc_pd_tgt pd' >>= fun pd_tgt ->
     printf "Target diagram: %s\n" (print_term_ctx pd_tgt);
     tc_with_vars pd_src (tc_infer_tm src) >>= fun (src_tm, src_typ) ->
     printf "Source term is: %s\n" (print_tm_term src_tm); 
     tc_with_vars pd_tgt (tc_infer_tm tgt) >>= fun (tgt_tm, tgt_typ) ->
     printf "Target term is: %s\n" (print_tm_term tgt_tm); 
     if (src_typ <> tgt_typ) then
       tc_fail "Source and target do not have the same type"
     else let pd_src_vars = SS.of_list (List.map fst pd_src) in
          let pd_tgt_vars = SS.of_list (List.map fst pd_tgt) in
          let src_vars = SS.union (tm_free_vars src_tm) (ty_free_vars src_typ) in
          let tgt_vars = SS.union (tm_free_vars tgt_tm) (ty_free_vars tgt_typ) in
          if (not (SS.subset pd_src_vars src_vars)) then
            tc_fail "Source is not algebraic"
          else if (not (SS.subset pd_tgt_vars tgt_vars)) then
            tc_fail "Target is not algebraic"
          else tc_ok (CompT (pd', ArrT (src_typ, src_tm, tgt_tm)))
                                      
(* Okay, here we need to generate a "standard form" for the variables
 * in a pasting diagram.  This is because we will need to compare them
 * during typing, and this has to be up to alpha equivalence.  I guess
 * indices would normally be the solution to this problem, but it turns
 * out that this makes calculating sources and targets *really* painful.
 *)                    
and tc_check_pd pd =
  match pd with
  | [] -> tc_fail "Empty context is not a pasting diagram"
  | (id, ObjE) :: [] -> tc_ok ((id, ObjT) :: [], id, ObjT)
  | (_, _) :: [] -> tc_fail "Pasting diagram does not begin with an object"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     tc_check_pd pd'                                          >>= fun (res_pd, pid, ptyp) ->
     tc_in_ctx res_pd (tc_check_ty tgt_typ)                   >>= fun tgt_typ_tm ->
     tc_in_ctx ((tgt_id, tgt_typ_tm) :: res_pd)
               (tc_check_ty fill_typ)                         >>= fun fill_typ_tm ->
     let cvars = List.map fst res_pd in 
     let codim = (dim_of ptyp) - (dim_of tgt_typ_tm) in
     tc_tgt_of (VarT pid) ptyp codim                          >>= fun (src_tm_tm, src_typ_tm) -> 
     if (tgt_typ_tm <> src_typ_tm) then
       let msg = sprintf "Type error: %s =/= %s"
                         (print_ty_term tgt_typ_tm) (print_ty_term src_typ_tm) in
       tc_fail msg
     else if (fill_typ_tm <> ArrT (src_typ_tm, src_tm_tm, VarT tgt_id)) then
       let msg = sprintf "Type error: %s =/= %s"
                         (print_ty_term (ArrT (src_typ_tm, src_tm_tm, VarT tgt_id)))
                         (print_ty_term fill_typ_tm) in
       tc_fail msg
     else if (fill_id = tgt_id) then
       tc_fail (sprintf "Fill and target cell have the same identifier: %s" fill_id)
     else if (List.mem fill_id cvars) then
       tc_fail (sprintf "Filling identifier %s already exists" fill_id)
     else if (List.mem tgt_id cvars) then 
       tc_fail (sprintf "Target identifier %s already exists" tgt_id)
     else tc_ok ((fill_id, fill_typ_tm) :: (tgt_id, tgt_typ_tm) :: res_pd, fill_id, fill_typ_tm)
        
(*
 *  Top-level command execution
 *)
                   
let rec check_cmds cmds =
  match cmds with
  | [] -> tc_ok ()
  | (CellDef (id, cell)) :: ds ->
     printf "-----------------\n";
     printf "Checking cell: %s\n" id;
     tc_check_cell cell >>= fun cell_tm ->
     printf "Ok!\n";
     tc_with_cell id cell_tm (check_cmds ds)
  | (TermDef (id, _, _, _)) :: ds ->
     printf "Skipping defined symbol: %s\n" id;
     check_cmds ds 


