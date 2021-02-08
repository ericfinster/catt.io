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
  | CohT of tm suite * tm * tm
  | PiT of tm * tm
  | LamT of tm 
  | AppT of tm * tm

(*****************************************************************************)
(*                              Semantic Domain                              *)
(*****************************************************************************)

type dom =
  | TypD
  | CatD
  | VarD of int
  | ObjD of dom
  | HomD of dom * dom * dom
  | CylD of dom
  | CohD of dom suite * dom * dom 
  | PiD of dom * (dom -> dom)
  | LamD of (dom -> dom)
  | AppD of dom * dom 

let appD f d =
  match f with
  | LamD phi -> phi d
  | _ -> AppD (f,d)

(*****************************************************************************)
(*                                  Readback                                 *)
(*****************************************************************************)

let rec rb k d =
  match d with
  | TypD -> TypT
  | CatD -> CatT
  | VarD i -> VarT (k - i - 1)
  | ObjD c -> ObjT (rb k c)
  | HomD (c,s,t) -> HomT (rb k c, rb k s, rb k t)
  | CylD c -> CylT (rb k c)
  | CohD (g,s,t) ->
    CohT (map (rb k) g, rb k s, rb k t)
  | PiD (a,p) -> PiT (rb k a, rb (k+1) (p (VarD k)))
  | LamD b -> LamT (rb (k+1) (b (VarD k)))
  | AppD (a,b) -> AppT (rb k a , rb k b)

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

(* rho is a suite of domain elements giving the bindings of variables *)
           
let rec eval tm rho =
  match tm with
  | TypT -> TypD
  | CatT -> CatD
  | VarT i -> nth i rho
  | ObjT cat -> ObjD (eval cat rho)
  | HomT (cat,src,tgt) ->
    HomD (eval cat rho, eval src rho, eval tgt rho)
  | CylT cat -> CylD (eval cat rho)
  | CohT (ctx,src,tgt) ->
    (* this one needs some thought ... *)
    CohD (map (fun t -> eval t rho) ctx, eval src rho, eval tgt rho)
  | PiT (a,p) -> PiD (eval a rho , fun d -> eval p (Ext (rho,d)))
  | LamT b -> LamD (fun d -> eval b (Ext (rho,d)))
  | AppT (a,b) -> appD (eval a rho) (eval b rho)
    
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
  gma : dom suite;
  rho : dom suite;
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

let tc_reify d env =
  let k = length (env.gma) in
  Ok (rb k d)

let tc_eval t env =
  Ok (eval t env.rho)

let tc_depth env =
  Ok (length (env.gma))
    
let tc_with tm ty m env =
  m { gma = Ext (env.gma,ty) ;
      rho = Ext (env.rho,tm) }
  
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
    let* (cat',_) = tc_check_tm cat CatD in
    tc_ok (ObjT cat')

  (* pi formation *)
  | PiT (a,p) ->
    let* a' = tc_check_ty a in
    let* ad = tc_eval a' in
    let* i = tc_depth in 
    let v = VarD i in
    tc_with ad v
      (let* p' = tc_check_ty p in 
       tc_ok (PiT (a',p')))

  | _ -> tc_throw (ExpectedType ty)
    
and tc_check_tm tm ty =
  match (tm,ty) with

  (* hom categories *)
  | (HomT (cat,src,tgt), CatD) ->
    let* (cat',_) = tc_check_tm cat CatD in
    let* cat_d = tc_eval cat' in 
    let* (src',_) = tc_check_tm src (ObjD cat_d) in
    let* (tgt',_) = tc_check_tm tgt (ObjD cat_d) in
    tc_ok (HomT (cat',src',tgt'), CatD)

  (* cylinder categories *)
  | (CylT cat, CatD) ->
    let* (cat',_) = tc_check_tm cat CatD in
    tc_ok (CylT cat', CatD)

  (* pi intro *)
  | (LamT b, PiD (a,p)) ->
    let* i = tc_depth in
    (* handle eta expansion ... *)
    let v = VarD i in 
    tc_with a v
      (let* (b',_) = tc_check_tm b (p v) in
       tc_ok (LamT b', PiD (a,p)))

  (* phase shift *)
  | _ ->
    let* (tm', ty') = tc_infer_tm tm in
    (* here we have to reify, i.e. readback and compare normal forms *)
    let* ty_nf = tc_reify ty in
    let* ty_nf' = tc_reify ty' in 
    if (ty_nf = ty_nf') then
      tc_ok (tm',ty')
    else
      tc_throw (TypeMismatch (tm,ty_nf,ty_nf'))

and tc_infer_tm tm =
  match tm with
  
  | VarT i ->
    let* typ = tc_lookup_var i in
    tc_ok (VarT i , typ)

  | _ -> tc_throw (InternalError "not done")
           
