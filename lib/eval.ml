(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Term
open Meta
open Value
open Suite
open Syntax
open Cylinder
open Pd

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

exception Eval_error of string

type unfolding = {
  level : int option;
  ufld_comp : bool;
  }

let decrease (ufld : unfolding) : unfolding = {
    level = Option.bind ufld.level (fun n -> Option.some (max 0 (n - 1)));
    ufld_comp = ufld.ufld_comp;
  }

let should_unfold (ufld: unfolding) : bool = not (Option.equal (=) ufld.level (Option.some 0))

let ufld_build n = {
    level = Option.some n;
    ufld_comp = true;
  }

let ufld_true = {
    level = Option.none;
    ufld_comp = true;
  }

let ufld_false = ufld_build 0

let rec eval top loc tm =
  (* pr "Evaluating: %a@," pp_term tm; *)
  match tm with
  | VarT i ->
    (try db_get i loc
     with Lookup_error ->
       raise (Eval_error (str "Index out of range: %d" i)))
  | TopT nm -> TopV (nm,EmpSp,(
      try assoc nm top
      with Lookup_error ->
        raise (Eval_error (str "Unknown id during eval: %s" nm))
    ))
  | LamT (nm,ict,u) -> LamV (nm, ict, Closure (top,loc,u))
  | AppT (u,v,ict) -> appV (eval top loc u) (eval top loc v) ict
  | PiT (nm,ict,u,v) -> PiV (nm, ict, eval top loc u, Closure (top,loc,v))
  | ObjT c -> ObjV (eval top loc c)
  | HomT (c,s,t) ->
    HomV (eval top loc c, eval top loc s, eval top loc t)

  | CylCohT (cn,pd,c,s,t) ->
    eval top loc
      (snd (TermCylCoh.cylcoh_impl cn pd c s t))

  | UCompT uc ->
    let v = eval top loc (term_ucomp (ucmp_pd uc)) in
    UCompV (uc, v, EmpSp)

  | CohT (nm,pd,c,s,t) ->

    let (loc',_) = Pd.fold_pd pd (Emp |> varV 0 , 1)
        ~f:(fun (args,l) _ -> (Ext (args, varV l) , l+1)) in

    let c' = eval top loc' c in
    let s' = eval top loc' s in
    let t' = eval top loc' t in

    CohV (nm,pd,c',s',t',EmpSp)

  | CylT (b,l,c) -> CylV (eval top loc b, eval top loc l, eval top loc c)
  | BaseT c -> baseV (eval top loc c)
  | LidT c -> lidV (eval top loc c)
  | CoreT c -> coreV (eval top loc c)
  | ArrT c -> ArrV (eval top loc c)
  | CatT -> CatV
  | TypT -> TypV
  | MetaT m -> metaV m
  | InsMetaT m -> appLocV loc (metaV m)

and metaV m =
  match lookup_meta m with
  | Unsolved -> FlexV (m, EmpSp)
  | Solved v -> v

and ($$) c v =
  match c with
  | Closure (top,loc,tm) -> eval top (Ext (loc,v)) tm

(* This must be somewhere already *)
and alt a b =
  match a with
  | Error x -> (match b with
                | Ok y -> Ok y
                | Error y -> Error (Printf.sprintf "%s | %s" x y))
  | Ok x -> Ok x

and appV t u ict =
  match t with
  | FlexV (m,sp) -> FlexV (m,AppSp(sp,u,ict))
  | RigidV (i,sp) -> RigidV (i,AppSp(sp,u,ict))
  | TopV (nm,sp,CohV (cn,pd,c,s,t,spc)) ->
     let sp' = AppSp (spc,u,ict) in
     let x = CohV (cn,pd,c,s,t,sp') in
     (match cohReduction cn pd c s t sp' u with
      | Error _ -> (* pr "No reduction: %a because %s\n\n" pp_value x y; *) TopV (nm,AppSp(sp,u,ict),x)
      | Ok y -> (* pr "Successful reduction %a to %a@," pp_value x pp_value y; *) y)
  | TopV (_,_,LamV(_,_,cl)) -> cl $$ u
  | TopV (nm,sp2,UCompV(ucd, CohV (cn,pd,c,s,t,spc), sp)) ->
     let sp' = AppSp (spc,u,ict) in
     (match cohReduction cn pd c s t sp' u with
      | Error _ -> TopV (nm, AppSp(sp2,u,ict), UCompV (ucd, CohV(cn,pd,c,s,t,sp'), AppSp(sp,u,ict)))
      | Ok y -> y
     )
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u,ict),appV tv u ict)
  | LamV (_,_,cl) -> cl $$ u
  | UCompV (ucd,CohV (cn,pd,c,s,t,spc),sp) ->
     let sp' = AppSp (spc,u,ict) in
     let x = CohV (cn,pd,c,s,t,sp') in
     (match cohReduction cn pd c s t sp' u with
      | Error _ -> UCompV(ucd, x, AppSp(sp,u,ict))
      | Ok y -> y)
  | CohV (cn,pd,c,s,t,sp) ->
     let sp' = AppSp(sp,u,ict) in
     let x = CohV (cn,pd,c,s,t,sp') in
     (match cohReduction cn pd c s t sp' u with
      | Error _ -> (* pr "No reduction: %a because %s\n\n" pp_value x y; *) x
      | Ok y -> y)
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

and cohReduction cn pd c s t sp' u =
  let* sp_list = sp_to_suite sp' in
  let k = length sp_list in
  if k = pd_length pd + 1 then
    alt (alt (insertionCoh cn pd c s t sp_list false) (disc_removal pd c s t u)) (endo_coherence_removal cn pd k c s t sp_list) else Error "Not applied all arguments yet"

and dim_ty ty =
    match ty with
    | HomV (c,_,_) -> dim_ty c + 1
    | _ -> 0

and unfold v =
    match force_meta v with
    | TopV (_,_,x) -> unfold x
    | UCompV (_,cohv,_) -> cohv
    | y -> y

and insertionCoh cn pd c s t args only_prune =

  let rec type_linearity c s t =
    match (unfold s, unfold t) with
    | (RigidV _, RigidV _) -> dim_ty c
    | _ -> match c with
           | HomV(c',s',t') -> type_linearity c' s' t'
           | _ -> -1 in

  let rec get_redex xs =
    match xs with
    | Emp -> Error "No redex found"
    | Ext (xs, ((_,_,_,_,t), redex_path)) when only_prune ->
       (match (unfold t) with
        | CohV (cn', pd', c', s', t', sp') ->
           let* args_inner = sp_to_suite sp' in
           let pda = map_pd_lvls pd' 1 ~f:(fun _ n _ (nm, ict) -> let (v,_) = nth n args_inner in (false, n , nm , ict, v)) in
           let dim = dim_pd pd' in
           let cond1 = is_disc pd' in
           let cond2 = is_same 0
                  (HomV (construct_disc_type dim, RigidV (2*dim + 1,EmpSp), RigidV (2*dim + 1,EmpSp)))
                  (HomV (c', s', t')) in
           if cond1 && cond2
           then Ok (cn', pd', c', s', t', pda, redex_path)
           else get_redex xs
        | _ -> get_redex xs)
    | Ext (xs, ((_,_,_,_,t), redex_path)) ->
       match (unfold t) with
       | CohV (cn', pd', c', s', t', sp') ->
          let* args_inner = sp_to_suite sp' in
          let pda = map_pd_lvls pd' 1 ~f:(fun _ n _ (nm, ict) -> let (v,_) = nth n args_inner in (false, n , nm , ict, v)) in
          if type_linearity c' s' t' >= length redex_path - 1 then Ok (cn', pd' ,c',s',t',pda ,redex_path) else get_redex xs
       | _ -> get_redex xs in

  let get_internal_substitution pd =
    let l = Pd.labels pd in
    let fl = filter (zip_with_idx l) (fun (_,(b,_,_,_,_)) -> not b) in
    map_suite_m (range 1 (length fl)) ~f:(fun n ->
        let* (x,(_,_,_,icit,_)) = find fl ~p:(fun (_,(_,i,_,_,_)) -> i = n) in
        Ok ((RigidV (x + 1,EmpSp),icit))) in

  let path_from_term_type tm ty path =
    let pl = length path in
    let ty_dim = dim_ty ty in
    let b = (first path = 1) in
    let d = ty_dim - pl in
    let rec go d ty =
      match ty with
      | HomV (c,s,t) -> if d > 0 then go (d-1) c else if b then Ok t else Ok s
      | _ -> Error "Internal error: path_from_term_type" in
    if pl > ty_dim then Ok tm else go d ty in

  let rec subtract_path path1 path2 =
    match (path1, path2) with
    | (Emp, _) -> Emp
    | (Ext (xs, x), Emp) -> Ext (xs, x)
    | (Ext (xs, x), Ext (ys, y)) -> Ext (subtract_path xs ys, x - y) in

  let get_external_substitution pd redex_path all_paths internal_tm internal_ty =
    let l = Pd.labels pd in
    let fl = filter (zip_with_idx l) (fun (_,(b,_,_,_,_)) -> b) in
    map_suite_m (range 1 (length all_paths)) ~f:(fun n ->
        match find fl ~p:(fun (_,(_,i,_,_,_)) -> i = n) with
        | Error _ ->
           let path = subtract_path (nth (n - 1) all_paths) redex_path in
           let* t = path_from_term_type internal_tm internal_ty path in
           Ok t
        | Ok (x,_) -> Ok (RigidV (x + 1,EmpSp))) in

  let ctx_length = pd_length pd + 1 in
  let pd_with_args = map_pd_lvls pd 1 ~f:(fun _ n _ (nm, ict) -> let (v,_) = nth n args in (true, n, nm, ict, v)) in

  match loc_max_bh pd_with_args with
  | Error _ -> Error "Pd is linear"
  | Ok xs ->
     let* (cni,pdi,ci,si,ti,redex_pd,redex_path) = get_redex xs in
     let internal_ctx_length = pd_length pdi + 1 in
     let internal_term = CohV(cni,pdi,ci,si,ti,EmpSp) in
     let* pd_insert = insertion pd_with_args redex_path redex_pd in
     let pd_final = map_pd pd_insert ~f:(fun (_,_,nm,icit,_) -> (nm,icit)) in
     let final_args = labels (map_pd pd_insert ~f:(fun (_,_,_,icit,v) -> (v,icit))) in
     let final_spine = suite_to_sp (append (singleton (first args)) final_args) in
     let* internal_sub_no_append = get_internal_substitution pd_insert in
     let internal_sub = append (singleton (RigidV (0, EmpSp), (snd cni))) internal_sub_no_append in
     let internal_term_subbed = runSpV internal_term (suite_to_sp internal_sub) in
     let internal_sub_no_icit = map_suite internal_sub ~f:fst in
     let civ = applySubstitution internal_ctx_length ci internal_sub_no_icit in
     let siv = applySubstitution internal_ctx_length si internal_sub_no_icit in
     let tiv = applySubstitution internal_ctx_length ti internal_sub_no_icit in
     let* external_sub_no_append = get_external_substitution pd_insert redex_path (get_all_paths pd) internal_term_subbed (HomV (civ,siv,tiv)) in
     let external_sub = append (singleton (RigidV (0,EmpSp))) external_sub_no_append in
     let cv = applySubstitution ctx_length c external_sub in
     let sv = applySubstitution ctx_length s external_sub in
     let tv = applySubstitution ctx_length t external_sub in
     Ok (runSpV (CohV(cn,pd_final,cv,sv,tv,EmpSp)) final_spine)

and applySubstitution k v sub =
  let t = quote ufld_true k v in
  eval Emp sub t

and construct_disc_type n =
  if n = 0 then RigidV (0, EmpSp) else HomV(construct_disc_type (n-1), RigidV (2*n - 1, EmpSp), RigidV (2*n,EmpSp) )

and disc_removal pd c s t u =


  if not (is_disc pd) then Error "Not disc"
  else
    if is_same 0 (HomV(c,s,t)) (construct_disc_type (dim_pd pd)) then Ok u
    else Error "Disc is not unbiased"

(* Can this somehow bu merged with unify? *)
and is_same l a b =
  match (unfold a, unfold b) with
  | (TypV , TypV) -> true
  | (CatV , CatV) -> true
  | (LamV (_,_,a) , LamV (_,_,a')) -> is_same (l + 1) (a $$ varV l) (a' $$ varV l)
  | (PiV (_,_,a,b), PiV (_,_,a',b')) -> is_same l a a' && is_same (l+1) (b $$ varV l) (b' $$ varV l)
  | (RigidV(i,sp), RigidV (i',sp')) when i = i' -> is_same_sp l sp sp'
  | (FlexV(m,sp), FlexV(m',sp')) when m = m' -> is_same_sp l sp sp'
  | (ObjV c, ObjV c') -> is_same l c c'
  | (HomV (c,s,t), HomV (c',s',t')) -> is_same l c c' && is_same l s s' && is_same l t t'
  | (ArrV c, ArrV c') -> is_same l c c'
  | (CohV (_,pd,c,s,t,sp), CohV (_,pd',c',s',t',sp')) when Pd.shape_eq pd pd' ->
     is_same l (HomV(c,s,t)) (HomV(c',s',t')) && is_same_sp l sp sp'
  | _ -> a = b

and is_same_sp l sp sp' =
  match (sp, sp') with
  | (EmpSp,EmpSp) -> true
  | (AppSp (s,u,_), AppSp (s', u', _)) -> is_same_sp l s s' && is_same l u u'
  | (BaseSp s, BaseSp s') -> is_same_sp l s s'
  | (LidSp s, LidSp s') -> is_same_sp l s s'
  | (CoreSp s, CoreSp s') -> is_same_sp l s s'
  | _ -> false

and endo_coherence_removal cn pd k c s t sp_list =
  (* Can't open syntax here: Must be a way to fix this *)
  let fresh_pd pd =
    let nm_lvl l = Fmt.str "x%d" l in
    Pd.map_pd_lf_nd_lvl pd
      ~lf:(fun lvl _ -> (nm_lvl lvl,Expl))
      ~nd:(fun lvl _ -> (nm_lvl lvl,Impl)) in
  let rec type_to_suite ty =
    match ty with
    | HomV(a,b,c) -> Ext(Ext(type_to_suite a, (b,Impl)), (c,Impl))
    | _ -> Emp in
  if not (is_same 0 s t) then Error "Not an endo coherence"
  else
    let dim = dim_ty c in
    let new_pd = fresh_pd (unit_disc_pd dim) in
    let coh_ty = construct_disc_type dim in
    let coh_ty_tm = RigidV(2*dim + 1,EmpSp) in
    if is_disc pd && c = coh_ty && s = coh_ty_tm then Error "Already identity"
    else
    let args_not_subbed = Ext(type_to_suite c, (s, Expl)) in
    let sp_list_no_icit = map_suite sp_list ~f:fst in
    let args_subbed = map_suite args_not_subbed ~f:(fun (v,i) -> (applySubstitution k v (sp_list_no_icit), i)) in
    let args_final = suite_to_sp (append (singleton (first sp_list)) args_subbed) in
    Ok (runSpV (CohV (cn,new_pd,coh_ty,coh_ty_tm,coh_ty_tm,EmpSp)) args_final)




and baseV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,BaseSp sp)
  | RigidV (i,sp) -> RigidV (i,BaseSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,BaseSp sp, baseV tv)
  | CylV (b,_,_) -> b
  | UCompV (ucd,cohv,sp) -> UCompV (ucd,baseV cohv,BaseSp sp)
  | CohV (cn,pd,sph,s,t,sp) ->
    CohV (cn,pd,sph,s,t,BaseSp sp)
  | _ -> raise (Eval_error "malformed base projection")

and lidV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,LidSp sp)
  | RigidV (i,sp) -> RigidV (i,LidSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,LidSp sp, lidV tv)
  | CylV (_,l,_) -> l
  | UCompV (ucd,cohv,sp) -> UCompV (ucd,lidV cohv,LidSp sp)
  | CohV (cn,pd,sph,s,t,sp) ->
    CohV (cn,pd,sph,s,t,LidSp sp)
  | _ -> raise (Eval_error "malformed lid projection")

and coreV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,CoreSp sp)
  | RigidV (i,sp) -> RigidV (i,CoreSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,CoreSp sp, coreV tv)
  | CylV (_,_,c) -> c
  | UCompV (ucd,cohv,sp) -> UCompV (ucd,coreV cohv,CoreSp sp)
  | CohV (cn,pd,sph,s,t,sp) ->
    CohV (cn,pd,sph,s,t,CoreSp sp)
  | _ ->
    let msg = Fmt.str "Cannot project core from: %a" pp_value v in
    raise (Eval_error msg)

and appLocV loc v =
  match loc with
  | Emp -> v
  | Ext (loc',u) -> appV (appLocV loc' v) u Expl

and runSpV v sp =
  match sp with
  | EmpSp -> v
  | AppSp (sp',u,ict) -> appV (runSpV v sp') u ict
  | BaseSp sp' -> baseV (runSpV v sp')
  | LidSp sp' -> lidV (runSpV v sp')
  | CoreSp sp' -> coreV (runSpV v sp')

and force_meta v =
  match v with
  | FlexV (m,sp) ->
    (match lookup_meta m with
     | Unsolved -> FlexV (m,sp)
     | Solved v -> force_meta (runSpV v sp))
  | _ -> v

(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

and quote (ufld : unfolding) k v =
  let dec_ufld = decrease ufld in
  let qc x = quote ufld k x in
  let qcs x s = quote_sp dec_ufld k x s in
  match force_meta v with
  | FlexV (m,sp) -> qcs (MetaT m) sp
  | RigidV (l,sp) -> qcs (VarT (lvl_to_idx k l)) sp
  | TopV (_,_,tv) when should_unfold ufld -> qc tv
  | TopV (nm,sp,_) -> qcs (TopT nm) sp
  | LamV (nm,ict,cl) -> LamT (nm, ict, quote ufld (k+1) (cl $$ varV k))
  | PiV (nm,ict,u,cl) -> PiT (nm, ict, qc u, quote ufld (k+1) (cl $$ varV k))
  | ObjV c -> ObjT (qc c)
  | HomV (c,s,t) -> HomT (qc c, qc s, qc t)

  | UCompV (_,cohv,_) when should_unfold ufld && ufld.ufld_comp ->
     qc cohv
  | UCompV (uc,_,sp) -> qcs (UCompT uc) sp

  | CohV (cn,pd,c,s,t,sp) ->

    let k' = length (Pd.labels pd) + 1 in
    let c' = quote dec_ufld k' c in
    let s' = quote dec_ufld k' s in
    let t' = quote dec_ufld k' t in

    qcs (CohT (cn,pd,c',s',t')) sp

  | CylV (b,l,c) -> CylT (qc b, qc l, qc c)
  | ArrV c -> ArrT (qc c)
  | CatV -> CatT
  | TypV -> TypT

and quote_sp ufld k t sp =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match sp with
  | EmpSp -> t
  | AppSp (sp',u,ict) ->
    AppT (qcs t sp',qc u,ict)
  | BaseSp sp' -> BaseT (qcs t sp')
  | LidSp sp' -> LidT (qcs t sp')
  | CoreSp sp' -> CoreT (qcs t sp')

let quote_tele tl =
  let rec go tl =
    match tl with
    | Emp -> (Emp,0)
    | Ext (typs',(nm,ict,typ)) ->
      let (r,k) = go typs' in
      let ty_tm = quote ufld_true k typ in
      (Ext (r,(nm,ict,ty_tm)),k+1)
  in fst (go tl)

let nf top loc tm =
  quote ufld_true (length loc) (eval top loc tm)

(*****************************************************************************)
(*                               Free Variables                              *)
(*****************************************************************************)

let rec free_vars_val k v =
  let module S = Base.Set in
  let fvc x = free_vars_val k x in
  let sp_vars sp = free_vars_sp k sp in
  match force_meta v with
  | FlexV (_,sp) -> sp_vars sp
  | RigidV (l,sp) -> S.add (sp_vars sp) (lvl_to_idx k l)
  | TopV (_,sp,_) -> sp_vars sp
  | LamV (_,_,Closure (_,loc,tm)) -> free_vars (length loc) tm
  | PiV (_,_,a,Closure (_,loc,b)) ->
    S.union (free_vars_val k a) (free_vars (length loc) b)
  | ObjV c -> free_vars_val k c
  | HomV (c,s,t) ->
    S.union_list (module Base.Int) [fvc c; fvc s; fvc t]
  | UCompV (_,_,sp) -> sp_vars sp
  | CohV (_,_,_,_,_,sp) -> sp_vars sp
  | CylV (b,l,c) ->
    S.union_list (module Base.Int) [fvc b; fvc l; fvc c]
  | ArrV c -> fvc c
  | CatV -> fvs_empty
  | TypV -> fvs_empty

and free_vars_sp k sp =
  let module S = Base.Set in
  let fvc x = free_vars_val k x in
  let fvcs x = free_vars_sp k x in
  match sp with
  | EmpSp -> fvs_empty
  | AppSp (sp',u,_) ->
    S.union (fvcs sp') (fvc u)
  | BaseSp sp' -> fvcs sp'
  | LidSp sp' -> fvcs sp'
  | CoreSp sp' -> fvcs sp'

(*****************************************************************************)
(*                            Value Pd Conversion                            *)
(*****************************************************************************)

module ValuePdSyntax = struct

  type s = value

  let cat = CatV
  let obj c = ObjV c
  let hom c s t = HomV (c,s,t)

  let match_hom v =
    match force_meta v with
    | HomV (c,s,t) -> Some (c,s,t)
    | _ -> None

  let match_obj v =
    match force_meta v with
    | ObjV c -> Some c
    | _ -> None

  let lift _ v = v
  let var _ l _ = RigidV (l,EmpSp)

  let strengthen _ _ _ _ =
    failwith "value strengthening not implemented"

  let pp_dbg = pp_value

end

module ValuePdUtil = PdUtil(ValuePdSyntax)

let string_pd_to_value_tele (c : string) (pd : string Pd.pd) : value tele =
  ValuePdUtil.string_pd_to_tele c pd


(*****************************************************************************)
(*                              Value Cylinders                              *)
(*****************************************************************************)

(* Do we not have something like this already? *)
let rec appArgs v args =
  match args with
  | Emp -> v
  | Ext (args',(ict,arg)) ->
    appV (appArgs v args') arg ict

module ValueCohSyntax = struct
  include ValuePdSyntax

  (* Separate coh implementation? *)
  let app u v ict = appV u v ict
  let coh cn pd c s t = CohV (cn,pd,c,s,t,EmpSp)
  let disc_coh cn pd =
    let t = TermUtil.disc_coh cn pd in
    eval Emp Emp t

end

module ValueCohUtil = CohUtil(ValueCohSyntax)

let value_ucomp (pd : 'a Pd.pd) : value =
  ValueCohUtil.gen_ucomp pd

module ValueCylinderSyntax = struct
  include ValueCohSyntax

  let arr v = ArrV v
  let cyl b l c = CylV (b,l,c)
  let base v = baseV v
  let lid v = lidV v
  let core v = coreV v

end

module ValueCyl = CylinderOps(ValueCylinderSyntax)

(* Revisit whether we really need these now ... *)
(* here, you could keep going and get a suspended one ... *)
let rec value_to_cyl_typ (cat : value) : (value * value cyl_typ , string) Result.t =
  match force_meta cat with
  | ArrV bc ->
    Ok (bc , Emp)
  | HomV (cat',s,t) ->
    let* (bc,ct) = value_to_cyl_typ cat' in
    Ok (bc, ct |> ((baseV s, lidV s, coreV s),
                   (baseV t, lidV t, coreV t)))
  | _ -> Error "Not a cylinder type"

let rec syntax_tree k v =
  match unfold v with
  | FlexV _ -> Ok "[]"
  | RigidV _ -> Ok "[]"
  | TopV (_,_,tv) -> syntax_tree k tv
  | LamV (_,_,cl) -> syntax_tree (k+1) (cl $$ varV k)
  | PiV (_,_,_,_) -> Error "No implementation"
  | ObjV c -> syntax_tree k c
  | HomV (_,s,t) ->
     let* s' = syntax_tree k s in
     let* t' = syntax_tree k t in
     Ok (String.concat "" [s';t'])
  | UCompV _ -> Error "No implementation"
  | CohV (_,_,_,s,t,sp) ->
     let* sp_suite = sp_to_suite sp in
     let* s' = syntax_tree k s in
     let* t' = syntax_tree k t in
     let* sp' = map_suite_m sp_suite ~f:(fun (v,ict) -> if ict = Expl then syntax_tree k v else Ok "") in
     Ok (Printf.sprintf "[%s%s%s]" s' t' (String.concat "" (to_list sp')))
  | _ -> Error "No implementaiton"
