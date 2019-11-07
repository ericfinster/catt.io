(*
 * typecheck.ml - catt typechecker
 *)

open Printf
open Common
open Syntax

module SS = Set.Make(String)
          
(* The typechecking monad *)
type 'a tcm = ctx -> 'a err

(* Bind for the typechecking monad *)
let ( >>= ) m f gma =
  match m gma with
  | Fail s -> Fail s
  | Succeed a -> f a gma
               
let tc_ok a = fun _ -> Succeed a
let tc_fail msg = fun _ -> Fail msg
let tc_in_ctx gma m = fun _ -> m gma
let tc_ctx = fun gma -> Succeed gma
let tc_with_var id ty m = fun gma -> m ((id, ty) :: gma)
                      
let rec tc_lookup ident gma =
  match gma with
  | [] -> Fail (Printf.sprintf "Unknown identifier: %s" ident)
  | (id,typ) :: gs ->
     if (id = ident) then
       Succeed typ
     else
       tc_lookup ident gs
    
    
(* Find the k-th target of the given term an type *)    
let rec tc_tgt_of a t k =
  if (k < 0) then
    tc_fail "Negative codimension"
  else if (k = 0) then
    tc_ok (a, t)
  else match t with
       | ObjT -> tc_fail "Object has no target"
       | ArrT (typ, _, tgt) -> tc_tgt_of tgt typ (k-1)

let tc_ctx_vars gma =
  Succeed (List.map fst gma)

let rec tc_pd_src k pd =
  match pd with
  | [] -> tc_fail "Empty pasting diagram"
  | (id, ObjT) :: [] -> tc_ok ((id, ObjT) :: [])
  | (_, _) :: [] -> tc_fail "Malformed pd"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     if (dim_of tgt_typ >= k) then
       tc_pd_src k pd'
     else
       tc_pd_src k pd' >>= fun pd_src ->
       tc_ok ((fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd_src)

let rec tc_pd_tgt k pd =
  match pd with
  | [] -> tc_fail "Empty pasting diagram"
  | (id, ObjT) :: [] -> tc_ok ((id, ObjT) :: [])
  | (_, _) :: [] -> tc_fail "Malformed pd"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     let d = dim_of tgt_typ in
     if (d > k) then
       tc_pd_tgt k pd'
     else tc_pd_tgt k pd' >>= fun pd_tgt ->
          if (d = k) then
            match pd_tgt with
            | [] -> tc_fail "Empty pasting diagram target"
            | _ :: pd_tgt' -> tc_ok ((tgt_id, tgt_typ) :: pd_tgt')
          else tc_ok ((fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd_tgt)

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
       
and tc_infer_tm x =
  match x with
  | VarE id -> 
     tc_lookup id >>= fun typ ->
     tc_ok (VarT id, typ)
  | DefAppE (id, args) -> tc_fail "unimplemented"
  | CellAppE (cell, args) -> tc_fail "unimplemented"

and tc_infer_cell c =
  match c with
  | CohE (pd, ty) -> tc_fail "unimplemented"
  | CompE (pd, ty) -> tc_fail "unimplemented"

and tc_check_pd pd =
  match pd with
  | [] -> tc_fail "Empty context is not a pasting diagram"
  | (id, ObjE) :: [] -> tc_ok ((id, ObjT) :: [], id, ObjT)
  | (_, _) :: [] -> tc_fail "Pasting diagram does not begin with an object"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     tc_check_pd pd'                                          >>= fun (res_pd, pid, ptyp) ->
     tc_in_ctx res_pd (tc_check_ty tgt_typ)                   >>= fun tgt_typ_tm ->
     tc_with_var tgt_id tgt_typ_tm (tc_check_ty fill_typ)     >>= fun fill_typ_tm ->
     tc_ctx_vars                                              >>= fun cvars ->
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
  | (Def (id, _, _)) :: ds ->
     printf "Passing coherence: %s\n" id;
     (* printf "Context: %s\n" (print_ctx ctx); *)
     (* (match ctx_to_pd ctx with *)
     (*  | Succeed (_, _, _) -> printf "Got a pasting diagram!\n" *)
     (*  | Fail msg -> printf "Error: %s\n" msg); *)
     check_cmds ds >>= fun _ -> tc_ok ()
  | (Let (id, _, _, _)) :: ds ->
     printf "Defining symbol: %s\n" id;
     check_cmds ds >>= fun _ -> tc_ok ()

