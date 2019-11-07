(*
 * typecheck.ml - catt typechecker
 *)

open Printf
open Common
open Syntax

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

(* Find the dimension of a regular type *)
let rec tc_dim_of typ =
  match typ with
  | ObjT -> tc_ok 0
  | ArrT (ty, _, _) ->
     tc_dim_of ty >>= fun d ->
     tc_ok (d + 1)
  | PiT (_, _) -> tc_fail "Dim of Pi"
    
(* Find the k-th target of the given term an type *)    
let rec tc_tgt_of a t k =
  if (k < 0) then
    tc_fail "Negative codimension"
  else if (k = 0) then
    tc_ok (a, t)
  else match t with
       | ObjT -> tc_fail "Object has no target"
       | ArrT (typ, _, tgt) -> tc_tgt_of tgt typ (k-1)
       | PiT (_, _) -> tc_fail "Pi has no target"

(* Will need freshness checking at some point ... *)                     
(* let rec is_fresh id pd = *)
(*   match pd with *)
(*   | PNil obj_id -> (obj_id <> id) *)
(*   | PCns (pd', (tgt_id, _), (fill_id, _)) -> *)
(*      (is_fresh id pd') && (tgt_id <> id) && (fill_id <> id) *)
                     
(* 
* Typechecking Rules
*)
    
let rec tc_check_ty t =
  match t with
  | ObjE -> tc_ok ObjT
  | ArrE (src, tgt) ->
     tc_infer_tm src >>= fun (src_tm, src_ty) ->
     tc_infer_tm tgt >>= fun (tgt_tm, tgt_ty) ->
     if (src_ty = tgt_ty) then
       tc_ok (ArrT (src_ty, src_tm, tgt_tm))
     else
       tc_fail "Ill-formed arrow type"

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
  | VarE id -> tc_fail "unimplemented" (* tc_lookup id *)
  | CellE cell -> tc_infer_cell cell
  | AppE (u, v) -> tc_fail "unimplemented"

and tc_infer_cell c =
  match c with
  | CohE (pd, ty) -> tc_fail "unimplemented"
  | CompE (pd, ty) -> tc_fail "unimplemented"

(* Hmm. Here we're not yielding a context written 
 * in some kind of de-brujin notation.  Should we?
 *
 * I mean, I feel like it basically just means accumulating
 * the length correctly, which should not really be hard.
 *)
                    
and tc_check_pd pd =
  match pd with
  | [] -> tc_fail "Empty context is not a pasting diagram"
  | (id, ObjE) :: [] -> tc_ok ((id, ObjT) :: [], id, ObjT)
  | (_, _) :: [] -> tc_fail "Pasting diagram does not begin with an object"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     tc_check_pd pd' >>= fun (res_pd, pid, ptyp) ->
     tc_in_ctx res_pd (tc_check_ty tgt_typ) >>= fun tgt_typ_tm ->
     tc_with_var tgt_id tgt_typ_tm (tc_check_ty fill_typ) >>= fun fill_typ_tm ->
     tc_dim_of ptyp >>= fun pd ->
     tc_dim_of tgt_typ_tm >>= fun td -> 
     let codim = pd - td in
     tc_tgt_of (FVarT pid) ptyp codim >>= fun (src_tm_tm, src_typ_tm) -> 
     (* if (tgt_typ_tm <> src_typ_tm) then *)
     (*   let msg = sprintf "Error while checking pasting diagram: %s =/= %s" *)
     (*                     (print_ty tgt_typ) (print_ty src_typ) in *)
     (*   tc_fail msg *)
     (* else if (fill_typ_tm <> ArrT (src_typ_tm, src_tm_tm, FVarT tgt_id)) *)
     
     tc_fail "unimplemented"


(* let rec ctx_to_pd gma = *)
(*   match gma with *)
(*   | [] -> Fail "Empty context is not a pasting diagram." *)
(*   | (id, Star) :: [] -> Succeed (PNil id, id, Star) *)
(*   | (_, Arrow (_, _, _)) :: [] -> Fail "Initial pasting diagram must be an object." *)
(*   | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: gma' -> *)
(*      printf "Target id: %s, Fill id: %s\n" tgt_id fill_id; *)
(*      ctx_to_pd gma' >>== fun (pd, pid, ptyp) -> *)
(*      let codim = (dim ptyp) - (dim tgt_typ) in *)
(*      tgt_of (Var pid) ptyp codim >>== fun (src_tm, src_typ) -> *)
(*      if (tgt_typ <> src_typ) then *)
(*        let msg = sprintf "Type error: %s =/= %s" *)
(*                          (print_ty tgt_typ) (print_ty src_typ) in  *)
(*        Fail msg *)
(*      else if (fill_typ <> Arrow (src_typ, src_tm, Var tgt_id)) then *)
(*        let msg = sprintf "Type error: %s =/= %s" *)
(*                          (print_ty (Arrow (src_typ, src_tm, Var tgt_id))) *)
(*                          (print_ty fill_typ) in  *)
(*        Fail msg *)
(*      else if (tgt_id = fill_id) then *)
(*        Fail (sprintf "Target and filling cell both have id: %s" tgt_id) *)
(*      else if (not (is_fresh tgt_id pd)) then *)
(*        Fail (sprintf "Duplicate target identifier: %s" tgt_id) *)
(*      else if (not (is_fresh fill_id pd)) then *)
(*        Fail (sprintf "Duplicate filling identifier: %s" fill_id) *)
(*      else Succeed (PCns (pd, (tgt_id, tgt_typ), (fill_id, fill_typ)), *)
(*                    fill_id, fill_typ) *)

        
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

