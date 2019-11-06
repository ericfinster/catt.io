(*
 * typecheck.ml - catt typechecker
 *)

open Printf
open Common
open Syntax

(* Old style syntax.  This will soon be replace ...*)
   
type ty =
  | Star
  | Arrow of ty * tm * tm

and tm =
  | Var of string
  | Coh of pd * ty * tm list
(* | Comp of pd * yt * tm list *)

and pd =
  | PNil of string
  | PCns of pd * (string * ty) * (string * ty)

type ctx = (string * ty) list
         
type decl =
  | Coh of string * ctx * ty

(* Pretty print terms, types and pasting diagrams. *)
let rec print_ty t =
  match t with
  | Star -> "*"
  | Arrow (t', src, tgt) ->
     sprintf "%s | %s -> %s" (print_ty t')
             (print_tm src) (print_tm tgt)

and print_tm t =
  match t with
  | Var s -> s
  | Coh (pd, typ, args) ->
     sprintf "(coh %s : %s)[%s]" (print_pd pd) (print_ty typ)
             (String.concat ", " (List.map print_tm args))

and print_pd pd =
  match pd with
  | PNil id -> sprintf "(%s : *)" id
  | PCns (pd', (tgt_id, tgt_typ), (fill_id, fill_typ)) ->
     sprintf "%s (%s : %s) (%s : %s)" (print_pd pd')
             tgt_id (print_ty tgt_typ)
             fill_id (print_ty fill_typ)

(* Print a context of variable declarations *)
let print_ctx gma =
  let prt_decl = fun (id, typ) ->
    sprintf "(%s : %s)" id (print_ty typ) in 
  String.concat " " (List.map prt_decl gma)
  
(* Return the dimension of a type expression *)
let rec dim typ =
  match typ with
  | Star -> 0
  | Arrow (t, _, _) -> 1 + (dim t)

                     
(*
 * Find the kth target of a term/type pair
 *)
let rec tgt_of a t k =
  if (k < 0) then
    Fail "Negative codimension"
  else if (k = 0) then
    Succeed (a, t)
  else match t with
       | Star -> Fail "Object has no target"
       | Arrow (typ, _, tgt) -> tgt_of tgt typ (k-1)

(* 
 * Check if the given identifier is fresh in 
 * the provided pasting diagram.
 *)
                              
let rec is_fresh id pd =
  match pd with
  | PNil obj_id -> (obj_id <> id)
  | PCns (pd', (tgt_id, _), (fill_id, _)) ->
     (is_fresh id pd') && (tgt_id <> id) && (fill_id <> id)
    
(* 
 * Attempt to convert a context into a pasting
 * diagram. Try to return a helpful message in 
 * case of failure.
 *)
    
let rec ctx_to_pd gma =
  match gma with
  | [] -> Fail "Empty context is not a pasting diagram."
  | (id, Star) :: [] -> Succeed (PNil id, id, Star)
  | (_, Arrow (_, _, _)) :: [] -> Fail "Initial pasting diagram must be an object."
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: gma' ->
     printf "Target id: %s, Fill id: %s\n" tgt_id fill_id;
     ctx_to_pd gma' >>== fun (pd, pid, ptyp) ->
     let codim = (dim ptyp) - (dim tgt_typ) in
     tgt_of (Var pid) ptyp codim >>== fun (src_tm, src_typ) ->
     if (tgt_typ <> src_typ) then
       let msg = sprintf "Type error: %s =/= %s"
                         (print_ty tgt_typ) (print_ty src_typ) in 
       Fail msg
     else if (fill_typ <> Arrow (src_typ, src_tm, Var tgt_id)) then
       let msg = sprintf "Type error: %s =/= %s"
                         (print_ty (Arrow (src_typ, src_tm, Var tgt_id)))
                         (print_ty fill_typ) in 
       Fail msg
     else if (tgt_id = fill_id) then
       Fail (sprintf "Target and filling cell both have id: %s" tgt_id)
     else if (not (is_fresh tgt_id pd)) then
       Fail (sprintf "Duplicate target identifier: %s" tgt_id)
     else if (not (is_fresh fill_id pd)) then
       Fail (sprintf "Duplicate filling identifier: %s" fill_id)
     else Succeed (PCns (pd, (tgt_id, tgt_typ), (fill_id, fill_typ)),
                   fill_id, fill_typ)

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
                             
let rec tc_lookup ident gma =
  match gma with
  | [] -> Fail (Printf.sprintf "Unknown identifier: %s" ident)
  | (id,typ) :: gs ->
     if (id = ident) then
       Succeed typ
     else
       tc_lookup ident gs

(* 
* Typechecking Rules
*)
    
let rec tc_check_ty t =
  match t with
  | Star -> tc_ok ()
  | Arrow (typ, src, tgt) ->
     tc_check_ty typ >>= fun _ ->
     tc_check_tm src typ >>= fun _ ->
     tc_check_tm tgt typ

and tc_check_tm x t =
  tc_infer x >>= fun xt ->
  if (xt = t) then tc_ok () else
    let msg = sprintf "The term %s was expected to have type %s, 
                       but was inferred to have type %s"
                      (print_tm x) (print_ty t) (print_ty xt) in 
    tc_fail msg
       
and tc_infer x =
  match x with
  | Var string -> tc_lookup string
  | Coh (_, _, _) -> tc_fail "unimplemented"

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

