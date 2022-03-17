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
open Pd

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

exception Eval_error of string

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
  | AppT (u,v,ict) -> fst (appV (eval top loc u) (eval top loc v) ict)
  | PiT (nm,ict,u,v) -> PiV (nm, ict, eval top loc u, Closure (top,loc,v))
  | ObjT c -> ObjV (eval top loc c)
  | HomT (c,s,t) ->
    HomV (eval top loc c, eval top loc s, eval top loc t)

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

and appV t u ict =
  match t with
  | FlexV (m,sp) -> (FlexV (m,AppSp(sp,u,ict)), false)
  | RigidV (i,sp) -> (RigidV (i,AppSp(sp,u,ict)), false)
  | TopV (nm,sp,tv) ->
     let (x, b) = appV tv u ict in
     if b then (x, true) else (TopV (nm,AppSp(sp,u,ict), x), false)
  | LamV (_,_,cl) -> (cl $$ u, true)
  | UCompV (ucd,cohv,sp) ->
     let (x, b) = appV cohv u ict in
     if b then (x, true) else (UCompV (ucd,x ,AppSp(sp,u,ict)), false)
  | CohV (cn,pd,c,s,t,sp) ->
     let sp' = AppSp(sp,u,ict) in
     (match cohReduction cn pd c s t sp' u with
      | Error _ -> (CohV (cn,pd,c,s,t,sp'),true)
      | Ok y -> (y, false))
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

and applySubstitution k v sub =
  let t = quote true k v in
  eval Emp sub t

(* This must be somewhere already *)
and alt a b =
  match a with
  | Error x -> (match b with
                | Ok y -> Ok y
                | Error y -> Error (Printf.sprintf "%s | %s" x y))
  | Ok x -> Ok x

and alt_list xs =
  match xs with
  | [] -> Error ""
  | (x :: xs) -> alt x (alt_list xs)

and cohReduction cn pd c s t sp' u =
  let* sp_list = sp_to_suite sp' in
  let k = length sp_list in
  if k = pd_length pd + 1
  then alt_list [
           insertion_reduction cn pd k c s t sp_list;
           disc_removal pd c s t u;
           endo_coherence_removal cn pd k c s t sp_list
         ]
  else Error "Not applied enough arguments yet"

and dim_ty ty =
    match ty with
    | HomV (c,_,_) -> dim_ty c + 1
    | _ -> 0

and unfold v =
    match force_meta v with
    | TopV (_,_,x) -> unfold x
    | UCompV (_,cohv,_) -> cohv
    | y -> y

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
    let new_pd = ValuePdUtil.fresh_pd (unit_disc_pd dim) in
    let coh_ty = construct_disc_type dim in
    let coh_ty_tm = RigidV(2*dim + 1,EmpSp) in
    if is_disc pd && c = coh_ty && s = coh_ty_tm then Error "Already identity"
    else
    let args_not_subbed = Ext(type_to_suite c, (s, Expl)) in
    let sp_list_no_icit = map_suite sp_list ~f:fst in
    let args_subbed = map_suite args_not_subbed ~f:(fun (v,i) -> (applySubstitution k v (sp_list_no_icit), i)) in
    let args_final = suite_to_sp (append (singleton (first sp_list)) args_subbed) in
    Ok (runSpV (CohV (cn,new_pd,coh_ty,coh_ty_tm,coh_ty_tm,EmpSp)) args_final)

and insertion_reduction cn pd k c s t sp_list =
  let rec get_redex (xs : ((name * icit * value) * mvar suite) suite) =
    match xs with
    | Emp -> Error "No redex found"
    | Ext (xs, ((_,_,x), redex_addr)) ->
       match (unfold v) with
       | CohV (cn', pd', c', s', t', sp') ->
          let* args_inner = sp_to_suite sp' in
          let pda = map_pd_lvls pd' 1 ~f:(fun _ n _ (x,y) -> (x, y, fst (nth n args_inner))) in
          if false then Ok (pda, redex_addr) else get_redex xs
       | _ -> get_redex xs in


  let pd_with_args = map_pd_lvls pd 1 ~f:(fun _ n _ (x,y) -> (x, y, fst (nth n sp_list))) in

  match loc_max_bh pd_with_args with
  | Error _ -> Error "Pd is linear"
  | Ok xs ->
     let* _ = get_redex xs in
     Error "TODO"

and appLocV loc v =
  match loc with
  | Emp -> v
  | Ext (loc',u) -> fst (appV (appLocV loc' v) u Expl)

and runSpV v sp =
  match sp with
  | EmpSp -> v
  | AppSp (sp',u,ict) -> fst (appV (runSpV v sp') u ict)

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

and quote ufld k v =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match force_meta v with
  | FlexV (m,sp) -> qcs (MetaT m) sp
  | RigidV (l,sp) -> qcs (VarT (lvl_to_idx k l)) sp
  | TopV (_,_,tv) when ufld -> qc tv
  | TopV (nm,sp,_) -> qcs (TopT nm) sp
  | LamV (nm,ict,cl) -> LamT (nm, ict, quote ufld (k+1) (cl $$ varV k))
  | PiV (nm,ict,u,cl) -> PiT (nm, ict, qc u, quote ufld (k+1) (cl $$ varV k))
  | ObjV c -> ObjT (qc c)
  | HomV (c,s,t) -> HomT (qc c, qc s, qc t)

  | UCompV (_,cohv,_) when ufld ->
     quote ufld k cohv
  | UCompV (uc,_,sp) -> qcs (UCompT uc) sp

  | CohV (cn,pd,c,s,t,sp) ->

    let k' = length (Pd.labels pd) + 1 in
    let c' = quote ufld k' c in
    let s' = quote ufld k' s in
    let t' = quote ufld k' t in

    qcs (CohT (cn,pd,c',s',t')) sp

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

let quote_tele tl =
  let rec go tl =
    match tl with
    | Emp -> (Emp,0)
    | Ext (typs',(nm,ict,typ)) ->
      let (r,k) = go typs' in
      let ty_tm = quote true k typ in
      (Ext (r,(nm,ict,ty_tm)),k+1)
  in fst (go tl)

let nf top loc tm =
  quote true (length loc) (eval top loc tm)

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

(*
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

end
 *)
