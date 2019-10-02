(*
 * typecheck.ml - catt typechecker
 *)

type ty =
  | Star
  | Arrow of ty * tm * tm

and tm =
  | Var of string
  | Coh of pd * ty * tm list

and pd =
  | PNil of string
  | PCns of pd * (string * ty) * (string * ty)

let rec dim typ =
  match typ with
  | Star -> 0
  | Arrow (t, _, _) -> 1 + (dim t)

type ctx = (string * ty) list
         
type decl =
  | Coh of string * ctx * ty

type 'a err =
  | Fail of string
  | Succeed of 'a
             
type 'a tcm = ctx -> 'a err

let ( >>= ) m f gma =
  match m gma with
  | Fail s -> Fail s
  | Succeed a -> f a gma
            
let tc_ok a = fun _ -> Succeed a
let tc_fail msg = fun _ -> Fail msg

let tc_in_ctx gma m = fun _ -> m gma
  
let rec tc_lookup ident gma =
  match gma with
  | [] -> Fail "Unknown identifier."
  | (id,typ) :: gs ->
     if (id == ident) then
       Succeed typ
     else
       tc_lookup ident gs

let rec tc_tgt_of a t k =
  if (k < 0) then
    tc_fail "negative codimension"
  else if (k == 0) then
    tc_ok (a, t)
  else match t with
       | Star -> tc_fail "no target of object"
       | Arrow (typ, _, tgt) -> tc_tgt_of tgt typ (k-1)
    
let rec check_ty t =
  match t with
  | Star -> tc_ok ()
  | Arrow (typ, src, tgt) ->
     check_ty typ >>= fun _ ->
     check_tm src typ >>= fun _ ->
     check_tm tgt typ

and check_tm x t =
  infer x >>= fun xt ->
  if (xt != t) then
    tc_fail "types do not match"
  else
    tc_ok ()
       
and infer x =
  match x with
  | Var string -> tc_lookup string
  | _ -> tc_fail "unimplemented"

(* Nice!  This is much simpler than your previous attempt
 * and would actually work for any context, since I think
 * it maintains the invariant that all terms appearing in
 * types are variables...
 *)
let rec check_pd p =
  match p with
  | PNil id -> tc_ok (id, Star)
  | PCns (ps, (tgt_id, tgt_typ), (fill_id, fill_typ)) ->
     check_pd ps >>= fun (id, typ) ->
     let codim = (dim typ) - (dim tgt_typ) in
     tc_tgt_of (Var id) typ codim >>= fun (src, src_typ) ->
     if (src_typ == tgt_typ) then
       if (fill_typ == Arrow (src_typ, src, Var tgt_id)) then
         (* Also much check freshness ...*)
         tc_ok (fill_id, fill_typ)
       else
         tc_fail "Bad filler declaration."
     else
       tc_fail "Bad target declaration."


let rec check_decls decls =
  match decls with
  | [] -> tc_ok ()
  | (Coh (id, _, _)) :: ds ->
     let () = Printf.printf "Passing coherence: %s\n" id in
     check_decls ds >>= fun _ -> tc_ok ()
