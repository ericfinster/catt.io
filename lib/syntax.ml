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

and tele = (ident * term) suite
    
type defn =
  | TermDef of string * tele * term * term
  | CohDef of string * tele * term

let rec map_bvar f tm =
  match tm with
  | TypT -> TypT
  | CatT -> CatT
  | VarT i -> VarT (f i)
  | IdT id -> IdT id
  | ObjT c -> ObjT (map_bvar f c)
  | HomT (c,s,t) ->
    HomT (Option.map (map_bvar f) c,
          map_bvar f s, map_bvar f t)
  | CylT c -> CylT (map_bvar f c)
  | CohT (pd,s,t) ->
    CohT (map (map_bvar f) pd,
          map_bvar f s, map_bvar f t)
  | PiT (i,a,p) -> PiT (i,map_bvar f a, map_bvar f p)
  | LamT (i,b) -> LamT (i,map_bvar f b)
  | AppT (u,v) -> AppT (map_bvar f u, map_bvar f v)

let db_lift k tm =
  map_bvar (fun i -> i + k) tm 
  
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
  | HomT (_,s,t) -> fprintf ppf "%a => %a"
                      pp_print_term s pp_print_term t
  | CylT c -> fprintf ppf "Cyl (%a)" pp_print_term c
  | CohT (_,_,_) -> fprintf ppf "coherence"
  | PiT (i,a,p) -> fprintf ppf "(%a : %a) -> %a"
                     pp_print_id_opt i
                     pp_print_term a
                     pp_print_term p
  | LamT (i,b) -> fprintf ppf "(\\%a. %a)"
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
    fprintf ppf "@[<hov>let %s %a : %a = %a@]" id
      pp_print_tele tl
      pp_print_term ty
      pp_print_term tm
  | CohDef (id,tl,ty) ->
    fprintf ppf "@[<hov>coh %s %a : %a@]" id
      pp_print_tele tl
      pp_print_term ty

(*****************************************************************************)
(*                           Context/Pd Conversion                           *)
(*****************************************************************************)

open Pd

module StrErr =
  ErrMnd(struct type t = string end)
    
let rec cat_dim t =
  let open MonadSyntax(StrErr) in 
  match t with
  | VarT _ -> Ok 0
  | HomT (Some c,_,_) ->
    let* d = cat_dim c in 
    Ok (d + 1)
  | _ -> Fail "no valid dimension"

let rec nth_tgt i ty tm =
  let open MonadSyntax(StrErr) in 
  if (i = 0) then Ok (ty, tm) else
    match ty with
    | HomT (Some c,_,t) ->
      nth_tgt (i-1) c t
    | _ -> Fail "No target"

let unobj t =
  let open MonadSyntax(StrErr) in 
  match t with
  | ObjT t' -> Ok t'
  | _ -> Fail "Not a type of objects"
           
let rec context_to_pd gma =
  let open MonadSyntax(StrErr) in 
  match gma with
  | Emp -> Fail "Empty context is not a pasting diagram"
  | Ext(Emp,_) -> Fail "Singleton context is not a pasting diagram"
  | Ext(Ext(Emp,CatT),ObjT (VarT 0)) ->
    Ok (Br (VarT 0,Emp),VarT 1,VarT 0,0,0)
  | Ext(Ext(gma',ttyp_ob),ftyp_ob) ->

    let* ttyp = unobj ttyp_ob in 
    let* ftyp = unobj ftyp_ob in
    
    let* (pd,styp,stm,k,dim) = context_to_pd gma' in
    let* tdim = cat_dim ttyp in
    let codim = dim - tdim in
    (* printf "k: %d@," k;
     * printf "codim: %d@," codim; *)
    let* (styp',stm') = nth_tgt codim styp stm in 
    (* printf "styp': %a@," pp_print_term styp';
     * printf "stm': %a@," pp_print_term stm'; *)
    if (styp' <> ttyp) then

      let msg = asprintf 
          "@[<v>Source and target types incompatible.
                @,Source: %a
                @,Target: %a@]"
          pp_print_term styp' pp_print_term ttyp
      in Fail msg

    else
      let lstyp = db_lift 1 styp' in
      let lstm = db_lift 1 stm' in 
      let etyp = HomT (Some lstyp, lstm, VarT 0) in
      if (ftyp <> etyp) then

        let msg = asprintf
            "@[<v>Incorrect filling type.
                  @,Expected: %a
                  @,Provided: %a@]"
            pp_print_term etyp
            pp_print_term ftyp
        in Fail msg

      else let* rpd = insert pd tdim (VarT (k+1)) (Br (VarT (k+2), Emp)) in 
        Ok (rpd, db_lift 1 ftyp, VarT 0, k+2, tdim+1)

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
  | VarT i -> db_get i tau
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
  | InternalError of string
  | ExpectedType of term
  | TypeMismatch of term * term * term
  | InvalidIndex of int
  | UnknownIdentifier of string
  | InferenceFailed of term

let pp_print_tc_err ppf terr =
  match terr with
  | ExpectedType tm ->
    fprintf ppf "Expected type: %a"
      pp_print_term tm
  | TypeMismatch (tm,tya,tyb) ->
    fprintf ppf "Type mismatch:@,@,@[<hov>%a@, =/= @,%a@]@,@,when checking@,@,%a"
      pp_print_term tya
      pp_print_term tyb
      pp_print_term tm 
  | InvalidIndex i ->
    fprintf ppf "Invalid index: %d" i
  | UnknownIdentifier id ->
    fprintf ppf "Unknown identifier: %s" id
  | InternalError s ->
    fprintf ppf "Internal error: %s" s
  | InferenceFailed tm ->
    fprintf ppf "Failed to infer type for: %a"
      pp_print_term tm 

let print_tc_err terr =
  pp_print_tc_err std_formatter terr
    
type tc_def =
  | CohDef of term suite * term * term
  | TmDef of term suite * term * term

type tc_env = {
  gma : (ident * term) suite;
  rho : glb_env;
}

let empty_env = { gma = Emp ; rho = Emp }
                
module TcmErr = ErrMnd(struct type t = tc_err end)
module TcmMnd = ReaderT(struct type t = tc_env end)(TcmErr)

open TcmMnd
open MonadSyntax(TcmMnd)

(***************************************************************************)
(*                          Typechecking Helpers                           *)
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
  try (let (_,_,ty) = glb_lookup id env.rho
       in tc_ok ty)
  with Not_found -> tc_throw (UnknownIdentifier id)

let rec tc_lookup_ctx_id k id g =
  match g with
  | Emp -> tc_throw (UnknownIdentifier id)
  | Ext (g',(id',d)) ->
    if (id = id') then
      tc_ok (k,d)
    else tc_lookup_ctx_id (k+1) id g'
    
let tc_reify d env =
  let k = length (env.gma) in
  TcmErr.pure (rb k d)

let tc_eval t env =
  (* eta expand the variables!!! *)
  let tau = map (fun (i,_) -> VarD i)
      (zip_with_idx env.gma) in 
  TcmErr.pure (eval t env.rho tau)

let tc_depth env =
  TcmErr.pure (length (env.gma))

let tc_with iopt ty m env =
  let nm = match iopt with
    | None -> ""
    | Some id -> id in 
  m { env with gma = Ext (env.gma,(nm,ty)) }

let tc_with_def id ty tm m env =
  m { env with rho = Ext (env.rho,(id,ty,tm)) }

let tc_with_env env m _ = m env

let tc_ctx_to_pd env =
  match context_to_pd (map snd env.gma) with
  | Fail msg -> Fail (InternalError msg)
  | Ok (pd,_,_,_,_) -> Ok pd 

let tc_dump_ctx env =
  printf "Context: @[<hov>%a@]@," pp_print_tele env.gma;
  Ok ()

(*****************************************************************************)
(*                               Normalization                               *)
(*****************************************************************************)

let tc_normalize tm =
  (* printf "About to normalize: %a@," pp_print_term tm; *)
  let* tmd = tc_eval tm in
  let* tm_nf = tc_reify tmd in
  (* printf "Result: %a@," pp_print_term tm_nf; *)
  tc_ok tm_nf

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
    let* cat' = tc_check_tm cat CatT in
    tc_ok (ObjT cat')

  (* pi formation *)
  | PiT (id,a,p) ->
    let* a' = tc_check_ty a in
    let* a_nf = tc_normalize a' in 
    tc_with id a_nf
      (let* p' = tc_check_ty p in 
       tc_ok (PiT (None, a',p')))

  (* fall back to inference *)
  | _ ->
    let* (ty',tty) = tc_infer_tm ty in
    (match tty with
     | TypT -> tc_ok ty'
     | _ -> tc_throw (ExpectedType ty))

and tc_check_tm tm ty =
  (* printf "Checking term: %a has type %a@,"
   *   pp_print_term tm pp_print_term ty; *)
  (* let* _ = tc_dump_ctx in  *)
  match (tm,ty) with

  | (_ , TypT) -> tc_check_ty tm 
    
  (* hom categories *)
  | (HomT (Some cat,src,tgt), CatT) ->
    let* cat' = tc_check_tm cat CatT in
    let* cat_nf = tc_normalize cat' in 
    let* src' = tc_check_tm src (ObjT cat_nf) in
    let* tgt' = tc_check_tm tgt (ObjT cat_nf) in
    tc_ok (HomT (Some cat',src',tgt'))
      
  (* hom category (inferred case) *)
  | (HomT (None,src,tgt), CatT) ->
    let* (src',src_ty) = tc_infer_tm src in
    (match src_ty with
     | ObjT cat ->
       let* tgt' = tc_check_tm tgt src_ty in
       tc_ok (HomT (Some cat,src',tgt'))
     | _ -> tc_throw (InternalError "not a category"))
  
  (* cylinder categories *)
  | (CylT cat, CatT) ->
    let* cat' = tc_check_tm cat CatT in
    tc_ok (CylT cat')

  (* pi intro *)
  | (LamT (id,b), PiT (_,a,p)) ->
    tc_with id a
      (let* b' = tc_check_tm b p in
       tc_ok (LamT (None,b')))

  (* phase shift *)
  | _ ->
    let* (tm', ty') = tc_infer_tm tm in
    let* ty_nf = tc_normalize ty in
    if (ty_nf = ty') then
      tc_ok tm'
    else
      (* has the unfortunate effect that we always print
       * error messages in fully normalized form ...
      *)
      tc_throw (TypeMismatch (tm,ty_nf,ty'))

and tc_infer_tm tm =
  (* printf "Inferring type of: %a@," pp_print_term tm; *)
  match tm with

  | IdT id ->
    let* env = tc_env in
    tc_try
      (let* (k,typ) = tc_lookup_ctx_id 0 id env.gma in
       let ty = db_lift (k+1) typ in 
       (* printf "Found a named variable of depth %d@," k;
        * printf "Context length is %d@," (length env.gma);
        * printf "Reified type: %a@," pp_print_term ty; *)
       tc_ok (VarT k,ty))
      (let* typ = tc_lookup_id id in
       (* Do we need to lift here? *)
       tc_ok (IdT id,typ))
       
  | VarT k ->
    (* let* env = tc_env in  *)
    let* typ = tc_lookup_var k in
    let ty = db_lift (k+1) typ in 
    tc_ok (VarT k,ty)

  | AppT (u,v) ->
    let* (u_tm,u_ty) = tc_infer_tm u in
    (match u_ty with
     | PiT (_,a,p) ->
       let* v_tm = tc_check_tm v a in
       let* app_ty = tc_normalize (AppT (LamT (None,p),v_tm)) in 
       tc_ok (AppT (u_tm,v_tm), app_ty)
     | _ -> tc_throw (InternalError "not a pi type"))

  | _ -> tc_throw (InferenceFailed tm)

(* m : term suite -> 'a tcm *)
let rec tc_with_tele tl m =
  match tl with
  | Emp -> m Emp
  | Ext(tl',(id,ty)) ->
    tc_with_tele tl'
      (fun s -> 
         let* ty' = tc_check_ty ty in
         let* ty_nf = tc_normalize ty' in 
         tc_with (Some id) ty_nf (m (Ext (s,ty_nf))))

(* to ignore the argument ... *)
let tc_in_tele tl m =
  tc_with_tele tl (fun _ -> m)
    
let rec abstract_all tl ty tm =
  match tl with
  | Emp -> (ty,tm)
  | Ext (tl',pty) ->
    abstract_all tl'
      (PiT (None,pty,ty)) (LamT (None,tm))

let tc_check_defn def =
  match def with
  | TermDef (id,tl,ty,tm) ->
    let* (tl',ty',tm') = tc_with_tele tl
        (fun tl' ->
           let* ty' = tc_check_ty ty in
           let* ty_nf = tc_normalize ty' in 
           let* tm' = tc_check_tm tm ty_nf in
           (* so we don't store the type in normal form. is this good? *)
           tc_ok (tl',ty',tm')) in
    let (rty,rtm) = abstract_all tl' ty' tm' in 
    tc_ok (id,rty,rtm)
  | CohDef (_,tl,_) ->
    let* env = tc_env in
    let* _ = tc_with_env { env with gma = Emp }
        (tc_in_tele tl
           (let* _ = tc_dump_ctx in 
            let* pd = tc_ctx_to_pd in
            printf "Pasting diagram: %a@,"
              (pp_print_pd pp_print_term) pd;
            tc_ok ()))
    in tc_throw (InternalError "not done")

let rec tc_check_defns defs =
  match defs with
  | [] -> tc_ok ()
  | d::ds ->
    print_string "-----------------";
    print_cut ();
    printf "Processing definition: @,%a@,"
      pp_print_defn d;
    let* (id,ty,tm) = tc_check_defn d in
    tc_with_def id ty tm (tc_check_defns ds)


    
