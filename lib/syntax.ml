(*****************************************************************************)
(*                                                                           *)
(*                                   Syntax                                  *)
(*                                                                           *)
(*****************************************************************************)

open Suite
open Mtl

(*****************************************************************************)
(*                        Internal Term Representation                       *)
(*****************************************************************************)

type tm =
  | TypT
  | CatT 
  | VarT of int
  | ObjT of tm 
  | HomT of tm * tm * tm
  | CylT of tm
  | PiT of tm * tm
  | AppT of tm * tm
  | CohT of tm suite * tm * tm

(*****************************************************************************)
(*                             Typechecking Monad                            *)
(*****************************************************************************)

type tc_err =
  | ExpectedType of tm
  | TypeMismatch of tm * tm * tm
  | InvalidIndex of int 
  | InternalError of string 

type tc_def =
  | CohDef of tm suite * tm * tm
  | TmDef of tm suite * tm * tm

type tc_env = {
  gma : tm suite;
  rho : (string * tc_def) suite;
}

module TcErrMnd = ErrMnd(struct type t = tc_err end)
module TcmMnd = ReaderT(struct type t = tc_env end)(TcErrMnd)

(* Bring syntax into scope *)
open TcmMnd
open MonadSyntax(TcmMnd)

type 'a tcm = 'a TcmMnd.m
    
let tc_ok a = pure a
let tc_throw e = lift (Fail e)

let tc_lookup_var i env =
  try Ok (nth i env.gma)
  with Not_found -> Fail (InvalidIndex i)


(*****************************************************************************)
(*                               Normalization                               *)
(*****************************************************************************)

let tc_normalize _ =
  tc_throw (InternalError "not done")

(*****************************************************************************)
(*                             Typechecking Rules                            *)
(*****************************************************************************)

let rec tc_check_ty ty = 
  match ty with

  (* type in type *)
  | TypT -> tc_ok TypT

  (* categories *)
  | CatT -> tc_ok CatT
  | ObjT cat ->
    let* (cat',_) = tc_check_tm cat CatT in
    tc_ok (ObjT cat')

  (* pi formation *)
  | PiT (a,b) ->
    let* a' = tc_check_ty a in
    (* extend context, etc here ... *)
    let* b' = tc_check_ty b in
    tc_ok (PiT (a',b'))

  | _ -> tc_throw (ExpectedType ty)
    
and tc_check_tm tm ty =
  match (tm,ty) with

  (* Hom Categories *)
  | (HomT (cat,src,tgt), CatT) ->
    let* (cat',_) = tc_check_tm cat CatT in
    let* (src',_) = tc_check_tm src (ObjT cat') in
    let* (tgt',_) = tc_check_tm tgt (ObjT cat') in
    tc_ok (HomT (cat',src',tgt'), CatT)

  (* phase shift *)
  | _ ->
    let* (tm', ty') = tc_infer_tm tm in
    let* ty_nf = tc_normalize ty in
    let* ty_nf' = tc_normalize ty' in 
    if (ty_nf = ty_nf') then
      tc_ok (tm',ty')
    else
      tc_throw (TypeMismatch (tm,ty,ty'))

and tc_infer_tm tm =
  match tm with
  
  | VarT i ->
    let* typ = tc_lookup_var i in
    tc_ok (VarT i , typ)

  | _ -> tc_throw (InternalError "not done")
           
