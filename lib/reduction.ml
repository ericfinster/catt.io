open Scheme
open Value
open Syntax
open Pd
open Suite

module Weak : ReductionScheme = struct
  let reductions cn pd k c s t sp = []
end

module rec StrictUnitAssoc : ReductionScheme = struct
  open Eval.Make(StrictUnitAssoc)

  let var n = RigidV(n,EmpSp)

  let applySubstitution k v sub =
    let t = quote true k v in
    eval Emp sub t

  let compose_subs k sub1 sub2 =
    map_suite sub1 ~f:(fun v -> applySubstitution k v sub2)

  let connect_pd (pd1 : 'a pd) (pd2 : 'a pd) : 'a pd =
    match (pd1,pd2) with
    | (Br(l,brs1), Br(l2,brs2)) -> Br (l,append brs1 brs2)

  let connect_right (pd1 : 'a pd) (pd2 : 'a pd) : value pd =
    let add_branch pd br =
      match pd with
      | Br (l,xs) -> Br (l,Ext(xs,br)) in

    let rec takeN n pd =
      match pd with
    | Br(l,Emp) -> Br (l,Emp)
    | Br(l,(Ext(brs,(l2,p)))) -> if n > 0 then add_branch (takeN (n-1) (Br(l,brs))) (l2,p) else Br(l2,Emp) in

    match pd2 with
    | Br (_,brs) -> takeN (length brs) (ValuePdUtil.args_pd (connect_pd pd1 pd2))

  let id_sub k =
    build_from_lvl ~f:(fun v -> RigidV(v , EmpSp)) (k + 1)

  let rec unfold v =
    match force_meta v with
    | TopV (_,_,x) -> unfold x
    | UCompV (_,cohv,_) -> cohv
    | y -> y

  (* Can this somehow bu merged with unify? *)
  let rec is_same l a b =
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

  let rec connect_subs sub1 sub2 =
    match sub2 with
    | Emp -> sub1
    | Ext(Emp,v) -> sub1
    | Ext(Ext(Emp,v1),v2) -> sub1
    | Ext(xs,v) -> Ext(connect_subs sub1 xs, v)

  let rec susp_tm v =
    match unfold v with
    | RigidV (l,EmpSp) -> var (l + 2)
    | CohV (cn,pd,c,s,t,sp) ->
       CohV (cn,Br(("*1",Impl),Ext(Emp,(("*2",Impl),pd))),susp_ty c, susp_tm s, susp_tm t, susp_sp sp)
    | x -> x

  and susp_ty v =
    match unfold v with
    | HomV(c,s,t) -> HomV(susp_ty c, susp_tm s, susp_tm t)
    | v -> HomV(v,var 1, var 2)

  and susp_sp sp =
    match sp with
    | EmpSp -> EmpSp
    | AppSp (EmpSp, v , icit) -> AppSp(AppSp(AppSp (EmpSp,v,icit),var 1,Impl),var 2,Impl)
    | AppSp (sp', v, icit) -> AppSp (susp_sp sp', susp_tm v, icit)

  and susp_sub sub =
    match sub with
    | Emp -> Emp
    | Ext(Emp,v) -> Ext(Ext(Ext(Emp,v),var 1), var 2)
    | Ext(xs,v) -> Ext(susp_sub xs, susp_tm v)

  let disc_removal : coh_reduction = fun cn pd k c s t sp ->
    if not (is_disc pd) then Error "Not disc"
    else
      if is_same 0 (HomV(c,s,t)) (ValueCohUtil.ucomp_ty cn pd) then ((* log_msg ~idt:2 "Completed disc"; *) Ok (fst (head sp)))
      else Error "Disc is not unbiased"

  let endo_coherence_removal cn pd k c s t sp_list =
    let rec type_to_suite ty =
      match ty with
      | HomV(a,b,c) -> Ext(Ext(type_to_suite a, (b,Impl)), (c,Impl))
      | _ -> Emp in
    if not (is_same 0 s t) then Error "Not an endo coherence"
    else
      let dim = ValuePdUtil.dim_ty c in
      let new_pd = ValuePdUtil.fresh_pd (unit_disc_pd dim) in
      let coh_ty = ValueCohUtil.ucomp_ty cn (new_pd) in
      let coh_ty_tm = var (2*dim + 1) in
      if is_disc pd && c = coh_ty && s = coh_ty_tm then Error "Already identity"
      else
        ((* log_val "ECR on" (CohV (cn,pd,c,s,t,EmpSp)) pp_value; *)
         let args_not_subbed = Ext(type_to_suite c, (s, Expl)) in
         (* log_val "args_not_subbed" (map_suite args_not_subbed ~f:fst) (pp_suite ~sep:Fmt.semi pp_value); *)
         let sp_list_no_icit = map_suite sp_list ~f:fst in
         (* log_val "sp_list_no_icit" sp_list_no_icit (pp_suite ~sep:Fmt.semi pp_value); *)
        let args_subbed = map_suite args_not_subbed ~f:(fun (v,i) -> (applySubstitution k v (sp_list_no_icit), i)) in
        let args_final = suite_to_sp (append (singleton (first sp_list)) args_subbed) in
        (* log_msg ~idt:2 "Completed ecr"; *)
        Ok (CohV (cn,new_pd,coh_ty,coh_ty_tm,coh_ty_tm,args_final)))

  let rec sub_from_sph sph =
    match sph with
    | Emp -> Ext (Emp, var 0)
    | Ext (xs, (a,b)) -> Ext(Ext(sub_from_sph xs,a),b)

  let sub_from_disc disc =
    match disc with
    | (sph,v) -> Ext (sub_from_sph sph,v)

  let tree_to_sub (v : 'a)(pd : 'a pd) : 'a suite =
    append (Ext (Emp,v)) (labels pd)

  let rec build_external_sub (cn : (name * icit))(pd : 'a pd) (path : int suite) (pd2 : 'a pd) : (value suite, string) result =
    match (pd, pd2, path) with
    | (Br (l, brs), Br (l2,brs2), Ext (Emp, n)) ->
       let (xs,ys) = split_suite (n + 1) brs in
       let* (y, xsd) = drop xs in
       let part1 = (id_sub (pd_length (Br (l,xsd)))) in
       let part2_1 = (sub_from_disc (ValueCohUtil.ucomp_with_type' (var 0) (ValuePdUtil.args_pd pd2) (dim_pd (snd (nth n brs)) + 1))) in
       let part2_2 = (tree_to_sub (var 0)(connect_right (Br (l,xsd)) (Br (l2,brs2)))) in
       let part2 = (compose_subs
                      (pd_length pd2 + 1)
                      part2_1 part2_2) in
       let part3 = (tree_to_sub (var 0)(connect_right (Br (l,append xsd brs2)) (Br(l,ys)))) in
       Ok (connect_subs (connect_subs part1 part2) part3)
    | (Br (l, brs), Br (l2, Ext (Emp, (l3,p2))), Ext(ns, n)) ->
       let (xs,ys) = split_suite (n+1) brs in
       let* ((_,br),xsd) = drop xs in
       let* pdr = insertion br ns p2 in
       let* ih = build_external_sub cn br ns p2 in
       let part1 = id_sub (pd_length (Br (l,xsd))) in
       let part2 = compose_subs (pd_length pdr + 3) (susp_sub ih) (tree_to_sub (var 0) (connect_right (Br (l,xsd)) (Br (l2,Ext(Emp,(l3,pdr)))))) in
       let part3 = tree_to_sub (var 0) (connect_right (Br (l, Ext (xsd, (l3,pdr)))) (Br(l,ys))) in
       Ok (connect_subs (connect_subs part1 part2) part3)
    | (_,_,_) -> Error "External sub failed"

  let insertion_reduction cn pd k c s t sp_list =
    let rec get_redex (xs : ((name * icit * value) * mvar suite) suite) =
      match xs with
      | Emp -> Error "No redex found"
      | Ext (xs, ((_,_,x), redex_addr)) ->
         match (unfold x) with
         | CohV (cn', pd', c', s', t', sp') ->
            if not (is_same 0 (HomV (c', s', t')) (ValueCohUtil.ucomp_ty cn' pd') || (is_disc pd' && is_same k c' (ValueCohUtil.ucomp_ty cn' pd') && is_same 0 s' (var (2*(dim_pd pd') + 1)) && is_same 0 s' t')) then get_redex xs else
              if linear_height pd' < length redex_addr - 1 then get_redex xs else
                let* args_inner = sp_to_suite sp' in
                let pda = map_pd_lvls pd' 1 ~f:(fun _ n _ (x,y) -> (x, y, fst (nth n args_inner))) in
                Ok (pda, redex_addr)
         | _ -> get_redex xs in

    let pd_with_args = map_pd_lvls pd 1 ~f:(fun _ n _ (x,y) -> (x, y, fst (nth n sp_list))) in
    match loc_max_bh pd_with_args with
    | Error _ -> Error "Pd is linear"
    | Ok xs ->
       let* (pd_inner_with_args, redex_addr) = get_redex xs in
       (* log_msg ~idt:2 "Attempting Insertion:"; *)
       (* log_val ~idt:4 "Outer pd" pd (pp_pd pp_nm_ict); *)
       (* log_val ~idt:4 "Inner pd" (map_pd pd_inner_with_args ~f:(fun (a,b,c) -> (a,b))) (pp_pd (pp_nm_ict)); *)
       (* log_val ~idt:4 "path" redex_addr (pp_suite Fmt.int); *)
       let* inserted_ctx_with_args = insertion pd_with_args redex_addr pd_inner_with_args in
       let* external_sub = build_external_sub cn pd_with_args redex_addr pd_inner_with_args in
       let nm_ict_tree = map_pd inserted_ctx_with_args ~f:(fun (a,b,c) -> (a,b)) in
       let follow_on_sp = suite_to_sp (map_suite ~f:(fun (a,b,c) -> (c,b)) (tree_to_sub (fst cn, snd cn, var 0) inserted_ctx_with_args)) in
       (* log_val ~idt:4 "Final tree" nm_ict_tree (pp_pd pp_nm_ict); *)
       (* log_val ~idt:4 "External sub" external_sub (pp_suite ~sep:Fmt.semi pp_value); *)
       (* log_val ~idt:4 "follow_on_sp" follow_on_sp (pp_spine_gen ~sep:Fmt.semi); *)
       (* log_val ~idt:4 "Eval c" c pp_value; *)
       let c' = applySubstitution k c external_sub in
       (* log_val ~idt:4 "c'" c' pp_value; *)
       (* log_val ~idt:4 "Eval s" s pp_value; *)
       let s' = applySubstitution k s external_sub in
       (* log_val ~idt:4 "s'" s' pp_value; *)
       (* log_val ~idt:4 "Eval t" t pp_value; *)
       let t' = applySubstitution k t external_sub in
       (* log_val ~idt:4 "t'" t' pp_value; *)
       (* log_msg ~idt:4 "Insertion done"; *)
       Ok (CohV (cn,
                 nm_ict_tree,
                 c',s',t',
                 follow_on_sp
         ))

  let reductions cn pd k c s t sp = [
      (fun _ -> disc_removal cn pd k c s t sp);
      (fun _ -> endo_coherence_removal cn pd k c s t sp);
      (fun _ -> insertion_reduction cn pd k c s t sp)
    ]
end
