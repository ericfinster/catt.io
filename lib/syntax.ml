(*****************************************************************************)
(*                                                                           *)
(*                                   Syntax                                  *)
(*                                                                           *)
(*****************************************************************************)

open Format
    
open Suite
open Mtl

(*****************************************************************************)
(*                                   Terms                                   *)
(*****************************************************************************)

type ident = string
  
type term =
  | TypT
  | CatT
  | VarT of int
  | IdT of ident
  | ObjT of term
  | HomT of term option * term * term
  | CylT of term
  | CohT of term suite * term * term
  | PiT of ident option * term * term
  | LamT of ident option * term
  | AppT of term * term

and tele = (string * term) suite
    
type defn =
  | TermDef of string * tele * term * term
  | CohDef of string * tele * term

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let is_app tm =
  match tm with
  | AppT (_,_) -> true
  | _ -> false
    
let rec pp_print_term ppf tm =
  
  match tm with
  | TypT -> fprintf ppf "U"
  | CatT -> fprintf ppf "Cat"
  | VarT i -> fprintf ppf "%d" i
  | IdT id -> fprintf ppf "%s" id
  | ObjT c -> fprintf ppf "[%a]" pp_print_term c
  | HomT (_,s,t) -> fprintf ppf "%a -> %a"
                      pp_print_term s pp_print_term t
  | CylT c -> fprintf ppf "Cyl (%a)" pp_print_term c
  | CohT (_,_,_) -> fprintf ppf "coherence"
  | PiT (i,a,p) -> fprintf ppf "(%a : %a) -> %a"
                     pp_print_id_opt i
                     pp_print_term a
                     pp_print_term p
  | LamT (i,b) -> fprintf ppf "\\%a. %a"
                    pp_print_id_opt i
                    pp_print_term b
  | AppT (u,v) ->
    if (is_app v) then
      fprintf ppf "%a (%a)" pp_print_term u
        pp_print_term v
    else
      fprintf ppf "%a %a" pp_print_term u
        pp_print_term v
           
and pp_print_id_opt ppf idopt =
  match idopt with 
  | None -> fprintf ppf "_"
  | Some id -> fprintf ppf "%s" id 

let pp_print_tele ppf tl =
  let pp_print_vdec pf (id , tm) =
    fprintf pf "(%s : %a)" id pp_print_term tm
  in pp_print_suite_custom "" false " " pp_print_vdec ppf tl

let pp_print_defn ppf def =
  match def with
  | TermDef (id,tl,ty,tm) ->
    fprintf ppf "let %s %a : %a = %a" id
      pp_print_tele tl
      pp_print_term ty
      pp_print_term tm
  | CohDef (_,_,_) ->
    fprintf ppf "coherence"

(*****************************************************************************)
(*                              Semantic Domain                              *)
(*****************************************************************************)

type dom =
  | TypD
  | CatD
  | VarD of int
  | ObjD of dom
  | HomD of dom option * dom * dom
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
  | HomD (None,s,t) -> HomT (None, rb k s, rb k t)
  | HomD (Some c,s,t) -> HomT (Some (rb k c), rb k s, rb k t)
  | CylD c -> CylT (rb k c)
  | CohD (g,s,t) ->
    CohT (map (rb k) g, rb k s, rb k t)
  | PiD (a,p) -> PiT (None, rb k a, rb (k+1) (p (VarD k)))
  | LamD b -> LamT (None, rb (k+1) (b (VarD k)))
  | AppD (a,b) -> AppT (rb k a , rb k b)

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

type lcl_env = dom suite
(* I mean, this should be changed to a list of definitions .... *)
type glb_env = (ident * term * term) suite

let rec glb_lookup id rho =
  match rho with
  | Emp -> raise Not_found
  | Ext (rho',(id',tm,ty)) ->
    if (id = id') then
      (rho',tm,ty)
    else glb_lookup id rho'
        
let rec eval tm rho tau =
  match tm with
  | TypT -> TypD
  | CatT -> CatD
  | VarT i -> nth i tau
  | IdT id ->
    let (rho',tm,_) = glb_lookup id rho in
    eval tm rho' Emp
  | ObjT cat -> ObjD (eval cat rho tau)
  | HomT (None,src,tgt) ->
    HomD (None, eval src rho tau, eval tgt rho tau)
  | HomT (Some cat,src,tgt) ->
    HomD (Some (eval cat rho tau), eval src rho tau, eval tgt rho tau)
  | CylT cat -> CylD (eval cat rho tau)
  | CohT (ctx,src,tgt) ->
    (* this one needs some thought ... *)
    CohD (map (fun t -> eval t rho tau) ctx, eval src rho tau, eval tgt rho tau)
  | PiT (_,a,p) -> PiD (eval a rho tau, fun d -> eval p rho (Ext (tau,d)))
  | LamT (_,b) -> LamD (fun d -> eval b rho (Ext (tau,d)))
  | AppT (a,b) -> appD (eval a rho tau) (eval b rho tau)

(*****************************************************************************)
(*                             Typechecking Monad                            *)
(*****************************************************************************)

type tc_err =
  | ExpectedType of term
  | TypeMismatch of term * term * term
  | InvalidIndex of int 
  | InternalError of string 

type tc_def =
  | CohDef of term suite * term * term
  | TmDef of term suite * term * term

type tc_env = {
  gma : (ident * dom) suite;
  rho : glb_env;
}

module TcmErr = ErrMnd(struct type t = tc_err end)
module TcmMnd = ReaderT(struct type t = tc_env end)(TcmErr)

open TcmMnd
open MonadSyntax(TcmMnd)

(***************************************************************************)
(*                             Monadic Helpers                             *)
(***************************************************************************)

let tc_ok a = pure a
let tc_throw e = lift (TcmErr.throw e)
let tc_env env = TcmErr.pure env
let tc_try m m' env =
  TcmErr.try_with (m env)
    (fun _ -> m' env)

let tc_lookup_var i env =
  try TcmErr.pure (snd (db_get i env.gma))
  with Not_found -> TcmErr.throw (InvalidIndex i)

let tc_lookup_id id =
  let* env = tc_env in
  try (let (rho',_,ty) = glb_lookup id env.rho
       in tc_ok (eval ty rho' Emp))
  with Not_found -> tc_throw (InternalError "unknown id")

let rec tc_lookup_ctx_id k id g =
  match g with
  | Emp -> tc_throw (InternalError "Unknown var id")
  | Ext (g',(id',d)) ->
    if (id = id') then
      tc_ok (k,d)
    else tc_lookup_ctx_id (k+1) id g'
    
let tc_reify d env =
  let k = length (env.gma) in
  TcmErr.pure (rb k d)

let tc_eval t env =
  (* eta expand the variables!!! *)
  let tau = map (fun (i,_) -> VarD (i-1))
      (zip_with_idx env.gma) in 
  TcmErr.pure (eval t env.rho tau)

let tc_depth env =
  TcmErr.pure (length (env.gma))

let tc_with iopt ty m env =
  let nm = match iopt with
    | None -> ""
    | Some id -> id in 
  m { env with gma = Ext (env.gma,(nm,ty)) }

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
  | PiT (id,a,p) ->
    let* a' = tc_check_ty a in
    let* ad = tc_eval a' in
    tc_with id ad
      (let* p' = tc_check_ty p in 
       tc_ok (PiT (None, a',p')))

  | _ -> tc_throw (ExpectedType ty)

and tc_check_tm tm ty =
  match (tm,ty) with

  (* hom categories *)
  (* | (HomT (cat,src,tgt), CatD) ->
   *   let* (cat',_) = tc_check_tm cat CatD in
   *   let* cat_d = tc_eval cat' in 
   *   let* (src',_) = tc_check_tm src (ObjD cat_d) in
   *   let* (tgt',_) = tc_check_tm tgt (ObjD cat_d) in
   *   tc_ok (HomT (cat',src',tgt'), CatD) *)

  (* cylinder categories *)
  | (CylT cat, CatD) ->
    let* (cat',_) = tc_check_tm cat CatD in
    tc_ok (CylT cat', CatD)

  (* pi intro *)
  | (LamT (id,b), PiD (a,p)) ->
    let* i = tc_depth in
    tc_with id a
      (let* (b',_) = tc_check_tm b (p (VarD i)) in
       tc_ok (LamT (None,b'), PiD (a,p)))

  (* phase shift *)
  | _ ->
    let* (tm', ty') = tc_infer_tm tm in
    let* ty_nf = tc_reify ty in
    let* ty_nf' = tc_reify ty' in 
    if (ty_nf = ty_nf') then
      tc_ok (tm',ty')
    else
      (* has the unfortunate effect that we always print
       * error messages in fully normalized form ...
      *)
      tc_throw (TypeMismatch (tm,ty_nf,ty_nf'))

and tc_infer_tm tm =
  match tm with

  | IdT id ->
    let* env = tc_env in
    tc_try
      (let* (k,typ) = tc_lookup_ctx_id 0 id env.gma in
       tc_ok (VarT k,typ))
      (let* typ = tc_lookup_id id in
       tc_ok (IdT id,typ))
       
  | VarT i ->
    let* typ = tc_lookup_var i in
    tc_ok (VarT i,typ)

  | _ -> tc_throw (InternalError "not done")

