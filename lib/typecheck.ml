(*****************************************************************************)
(*                                                                           *)
(*                           Typechecking Routines                           *)
(*                                                                           *)
(*****************************************************************************)

open Scheme

module Make(R : ReductionScheme) = struct
open Fmt

open Base
open Suite
open Expr
open Term
open Value
open Meta
open Eval.Make(R)
open Unify.Make(R)
open Syntax

(* Monadic bind for errors in scope *)
let (let*) m f = Base.Result.bind m ~f

(*****************************************************************************)
(*                                  Contexts                                 *)
(*****************************************************************************)

type bd =
  | Bound
  | Defined

type ctx = {
  top : top_env;
  loc : loc_env;
  lvl : lvl;
  types : (name * (bd * value)) suite;
}

let empty_ctx = {
  top = Emp;
  loc = Emp;
  lvl = 0;
  types = Emp;
}

let empty_loc gma = {
  top = gma.top;
  loc = Emp;
  lvl = 0;
  types = filter gma.types
      (fun (_,(bd,_)) ->
         match bd with
         | Defined -> true
         | Bound -> false)

}

let bind gma nm ty =
  let l = gma.lvl in {
    loc = Ext (gma.loc, varV l);
    top = gma.top;
    lvl = l+1;
    types = Ext (gma.types,(nm,(Bound,ty)));
  }

let define gma nm tm ty = {
  loc = gma.loc;
  top = Ext (gma.top,(nm,tm));
  lvl = gma.lvl;
  types = Ext (gma.types,(nm,(Defined,ty)));
}

let names gma =
  map_suite gma.types ~f:fst

(*****************************************************************************)
(*                                   Debug                                   *)
(*****************************************************************************)

let rec quote_types ufld typs =
  match typs with
  | Emp -> (Emp,0)
  | Ext (typs', (nm, (Defined,typ))) ->
    let (res_typs, l) = quote_types ufld typs' in
    let typ_tm = quote ufld l typ in
    (Ext (res_typs,(nm,typ_tm)),l)
  | Ext (typs', (nm, (_,typ))) ->
    let (res_typs, l) = quote_types ufld typs' in
    let typ_tm = quote ufld l typ in
    (Ext (res_typs,(nm, typ_tm)),l+1)

let dump_ctx ufld gma =
  let (tl,_) = quote_types ufld gma.types in
  pr "Context: @[<hov>%a@]@,"
    (pp_suite (parens (pair ~sep:(any " : ") string pp_term))) tl

(*****************************************************************************)
(*                                Typechecking                               *)
(*****************************************************************************)

let fresh_meta _ =
  let mctx = ! metacontext in
  let m = ! next_meta in
  next_meta := m + 1;
  (* pr "next meta set to: %d@," (! next_meta); *)
  metacontext := Map.set mctx ~key:m ~data:Unsolved;
  InsMetaT m

(* used for generating unknown categories.... *)
let obj_meta gma typ =
  let bc = eval gma.top gma.loc (fresh_meta ()) in
  unify OneShot gma.top gma.lvl typ (ObjV bc);
  bc

let rec insert' gma m =
  let* (tm, ty) = m in
  match force_meta ty with
  | PiV (_,Impl,_,b) ->
    let m = fresh_meta () in
    let mv = eval gma.top gma.loc m in
    insert' gma (Ok (AppT (tm,m,Impl) , b $$ mv))
  | _ -> Ok (tm, ty)

let insert gma m =
  let* (tm, ty) = m in
  match tm with
  | LamT (_,Impl,_) -> Ok (tm, ty)
  | _ -> insert' gma (Ok (tm, ty))

type typing_error = [
  | `NameNotInScope of name
  | `IcityMismatch of icit * icit
  | `TypeMismatch of string
  | `PastingError of string
  | `FullnessError of string
  | `NotImplemented of string
  | `BadCohQuot of string
  | `InternalError
  | `AssertError of value * value
]

let pp_error ppf e =
  match e with
  | `NameNotInScope nm -> Fmt.pf ppf "Name not in scope: %s" nm
  | `TypeMismatch msg -> Fmt.pf ppf "%s" msg
  | `PastingError msg -> Fmt.pf ppf "Error while checking pasting context: %s" msg
  | `FullnessError msg -> Fmt.pf ppf "Fullness error: %s" msg
  | `IcityMismatch (_, _) -> Fmt.pf ppf "Icity mismatch"
  | `BadCohQuot msg -> Fmt.pf ppf "%s" msg
  | `NotImplemented f -> Fmt.pf ppf "Feature not implemented: %s" f
  | `InternalError -> Fmt.pf ppf "Internal Error"
  | `AssertError (v1, v2) -> Fmt.pf ppf "Assertion Error, %a and %a were not equal" pp_value v1 pp_value v2

let rec check gma expr typ =
  let typ_tm = quote false gma.lvl typ in
  let typ_expr = term_to_expr (names gma) typ_tm in
  (* pr "Checking @[%a@] has type @[%a@]@," pp_expr_with_impl expr pp_expr_with_impl typ_expr ; *)

  let switch e expected =
    (* pr "switching mode@,"; *)
    (* pr "e: %a@," pp_expr e; *)
    (* pr "exp: %a@," pp_term (quote false gma.lvl expected); *)
    let* (e',inferred) = insert gma (infer gma e) in
    try unify UnfoldAll gma.top gma.lvl expected inferred ; Ok e'
    with Unify_error msg ->
      pr "Unification error: %s\n" msg;
      (* I guess the unification error will have more information .... *)
      let nms = names gma in
      let inferred_nf = term_to_expr nms (quote false gma.lvl inferred) in
      let expected_nf = term_to_expr nms (quote false gma.lvl expected) in
      let does_equal = (Poly.(=) (quote true gma.lvl inferred) (quote true gma.lvl expected)) in
      let msg = String.concat [ str "@[<v>The expression: @,@, @[%a@]@,@,@]" pp_expr_with_impl e;
                                str "@[<v>has type: @,@,  @[%a@]@,@,@]" pp_expr_with_impl inferred_nf;
                                str "@[<v>but was expected to have type: @,@, @[%a@]@,@]" pp_expr_with_impl expected_nf;
                                str "@[<v>Do these have same normal form: %a]" Fmt.bool does_equal
                                  ]

      in Error (`TypeMismatch msg)
  in

  match (expr, force_meta typ) with

  | (e , TopV (_,_,tv)) ->
    check gma e tv

  | (LamE (nm,i,e) , PiV (_,i',a,b)) when Poly.(=) i i' ->
    let* bdy = check (bind gma nm a) e (b $$ varV gma.lvl) in
    Ok (LamT (nm,i,bdy))

  | (t , PiV (nm,Impl,a,b)) ->
    let* bdy = check (bind gma nm a) t (b $$ varV gma.lvl) in
    Ok (LamT (nm,Impl,bdy))

  | (HoleE , _) -> (* pr "fresh meta@,"; *)
    let mv = fresh_meta () in Ok mv

  | (e, expected) -> switch e expected

and infer gma expr =
  (* pr "@[<v>Inferring type of: @[%a@]@, in: @[%a@]@,@]" *)
  (*   pp_expr_with_impl expr (pp_suite Fmt.string) (map_suite ~f:(fun (idx,_) -> idx) gma.types); *)
  match expr with

  | VarE nm -> (
      try
        let (idx,(b,typ)) = assoc_with_idx nm gma.types in
        match b with
        | Bound -> Ok (VarT idx, typ)
        | Defined -> Ok (TopT nm, typ)
      with Lookup_error -> Error (`NameNotInScope nm)
    )

  | LamE (nm,ict,e) ->
    let a = eval gma.top gma.loc (fresh_meta ()) in
    let* (e', t) = insert gma (infer (bind gma nm a) e) in
    let cl = Closure (gma.top,gma.loc,quote false (gma.lvl + 1) t) in
    Ok (LamT (nm,ict,e') , PiV (nm,ict,a,cl))

  | AppE (u,v,ict) ->
    let* (u',ut) = match ict with
      | Impl -> infer gma u
      | Expl -> insert' gma (infer gma u)
    in
    let* (a,b) = match force_meta ut with
      | PiV (_,ict',a,b) ->
        if (Poly.(<>) ict ict') then
          Error (`IcityMismatch (ict,ict'))
        else Ok (a,b)
      | _ ->
        let a = eval gma.top gma.loc (fresh_meta ()) in
        let b = Closure (gma.top,gma.loc,fresh_meta ()) in
        unify OneShot gma.top gma.lvl ut (PiV ("x",ict,a,b));
        Ok (a,b)
    in let* v' = check gma v a in
    Ok (AppT (u', v', ict) , b $$ eval gma.top gma.loc v')

  | PiE (nm,ict,a,b) ->
    let* a' = check gma a TypV in
    let* b' = check (bind gma nm (eval gma.top gma.loc a')) b TypV in
    Ok (PiT (nm,ict,a',b') , TypV)

  | ObjE c ->
    let* c' = check gma c CatV in
    Ok (ObjT c', TypV)

  | HomE (c,s,t) ->
    let* c' = check gma c CatV in
    let cv = eval gma.top gma.loc c' in
    let* s' = check gma s (ObjV cv) in
    let* t' = check gma t (ObjV cv) in
    Ok (HomT (c',s',t'), CatV)

  | UCompE (UnitPd pd) ->
    let e = expr_ucomp pd in
    pr "@[<v>Generated ucomp: @[%a]@,@]" pp_expr e;
    let* (tm,ty) = infer gma e in
    pr "@[<b>Result of inferrence: @[%a]@,@]" pp_term tm;
    Ok (UCompT (UnitPd pd),ty)

  | UCompE (DimSeq ds) ->
    let pd = Pd.comp_seq ds in
    let e = expr_ucomp pd in
    pr "@[<v>Generated ucomp: @[%a]@,@]" pp_expr e;
    let* (_,ty) = infer gma e in
    Ok (UCompT (DimSeq ds),ty)

  | CohE (g,c,s,t) ->
    let* (tl,pd,ct,st,tt) = check_coh gma g c s t in
    let coh_ty = eval gma.top gma.loc
        (tele_to_pi tl (ObjT (HomT (ct,st,tt)))) in
    let ty_nf = term_to_expr Emp (quote false gma.lvl coh_ty) in
    (* pr "@[<v>Coherence: @[%a@]@,inferred to have type: @[%a@]@,@]" *)
    (*   pp_expr_with_impl (CohE (g,c,s,t)) pp_expr_with_impl ty_nf; *)
    Ok (CohT (pd,ct,st,tt) , coh_ty)

  | ArrE c ->
    let* c' = check gma c CatV in
    Ok (ArrT c' , CatV)

  | StarE -> Ok (StarT , CatV)
  | CatE -> Ok (CatT, TypV)
  | TypE -> Ok (TypT , TypV)

  | HoleE ->
    let a = eval gma.top gma.loc (fresh_meta ()) in
    let t = fresh_meta () in
    Ok (t , a)

and with_tele : 'a . ctx -> expr tele
  -> (ctx -> value tele -> term tele -> ('a,typing_error) Result.t)
  -> ('a,typing_error) Result.t = fun gma tl m ->
  match tl with
  | Emp -> m gma Emp Emp
  | Ext (tl',(id,ict,ty)) ->
    with_tele gma tl' (fun g tv tt ->
        let* ty_tm = check g ty TypV in
        let ty_val = eval g.top g.loc ty_tm in
        m (bind g id ty_val)
          (Ext (tv,(id,ict,ty_val)))
          (Ext (tt,(id,ict,ty_tm))))

and check_coh gma g c s t =
  (* pr "@[<v>check_coh@,gma: @[%a@]@,c: @[%a@]@,s: @[%a@]@,t: @[%a@]@,@]" *)
  (*   (pp_tele pp_expr) g pp_expr c pp_expr s pp_expr t; *)
  with_tele (empty_loc gma) g (fun gma' gv tl ->

      (* pr "@[<v>gv: @[%a@]@,@]" (pp_tele pp_value) gv; *)

      match ValuePdUtil.tele_to_pd gv with
      | Error msg -> Error (`PastingError msg)
      | Ok pd ->

        (* pr "@[<v>pd: %a@,@]" (Pd.pp_pd (pair string pp_ict)) pd; *)

        let lc = gma'.loc in
        let tp = gma'.top in

        let cat_idx = length gv - 1 in
        let ipd = idx_pd pd in

        let* c' = check gma' c CatV in
        let cv = eval tp lc c' in

        (* pr "@[<v>About to check src and tgt@,cv: %a@,@]" pp_value (force_meta cv); *)
        let* s' = check gma' s (ObjV cv) in
        let* t' = check gma' t (ObjV cv) in

        (* pr "@[<v>source: %a@,@]" pp_term s'; *)
        (* pr "@[<v>target: %a@,@]" pp_term t'; *)

        let sv = eval tp lc s' in
        let tv = eval tp lc t' in

        (* pr "@[<v>cv: %a@,@]" pp_value (force_meta cv); *)

        let sph = ValuePdUtil.match_homs cv in

        (* pr "@[<v>sph: %a@,@]" pp_value bc; *)

            let k = length gma'.loc in
            let cat_vars = free_vars_val k cv in
            let src_vars = free_vars_val k sv in
            let tgt_vars = free_vars_val k tv in
            let pd_dim = Pd.dim_pd pd in

            if (length sph + 1 > pd_dim) then
              (* Coherence Case *)
              let pd_vars = Pd.fold_pd ipd fvs_empty
                  ~f:(fun vs i -> Set.add vs i) in
              let tot_src_vars = Set.union cat_vars src_vars in
              let tot_tgt_vars = Set.union cat_vars tgt_vars in
              if (not (Set.is_subset pd_vars ~of_:tot_src_vars) ||
                  not (Set.is_subset pd_vars ~of_:tot_tgt_vars)) then
                Error (`FullnessError "coherence case is not full")
              else Ok (tl,pd,c',s',t')

            else

              let pd_src = Pd.truncate true (pd_dim - 1) ipd in
              let pd_tgt = Pd.truncate false (pd_dim - 1) ipd in

              let pd_src_vars = Pd.fold_pd pd_src (fvs_singleton cat_idx)
                  ~f:(fun vs i -> Set.add vs i) in
              let pd_tgt_vars = Pd.fold_pd pd_tgt fvs_empty
                  ~f:(fun vs i -> Set.add vs i) in

              let tot_src_vars = Set.union cat_vars src_vars in
              let tot_tgt_vars = Set.union cat_vars tgt_vars in

              if (not (Set.is_subset pd_src_vars ~of_:tot_src_vars)) then
                let msg = Fmt.str "@[<v>Non-full source:@,pd: @[%a@]@,src: @[%a@]@,"
                    (pp_tele pp_expr) g pp_expr s in
                Error (`FullnessError msg)
              else if (not (Set.is_subset pd_tgt_vars ~of_:tot_tgt_vars)) then
                let msg = Fmt.str "@[<v>Non-full target:@,pd: @[%a@]@,tgt: @[%a@]@,"
                    (pp_tele pp_expr) g pp_expr t in
                Error (`FullnessError msg)
              else Ok (tl,pd,c',s',t')
    )

and check_sph gma sph c =
  match sph with
  | Emp -> Ok (c,Emp)
  | Ext (sph',(s,t)) ->
    let* (c',sph'') = check_sph gma sph' c in
    let* s' = check gma s (ObjV c') in
    let sv = eval gma.top gma.loc s' in
    let* t' = check gma t (ObjV c') in
    let tv = eval gma.top gma.loc t' in
    Ok (HomV (c',sv,tv), Ext (sph'',(s',t')))

and check_cyl_coh gma g c (ssph,s) (tsph,t) =
  (* pr "@[<v>check_cyl_coh@,gma: @[%a@]@,c: @[%a@]@,s: @[%a@]@,t: @[%a@]@,@]"
   *   (pp_tele pp_expr) g pp_expr c pp_expr s pp_expr t; *)
  with_tele (empty_loc gma) g (fun gma' gv gt ->

      match ValuePdUtil.tele_to_pd gv with
      | Error msg -> Error (`PastingError msg)
      | Ok pd ->

        let lc = gma'.loc in
        let tp = gma'.top in

        let cat_idx = length gv - 1 in
        let ipd = idx_pd pd in

        let* c' = check gma' c CatV in
        let cv = eval tp lc c' in

        let* (scatv,ssph') = check_sph gma' ssph cv in
        let* (tcatv,tsph') = check_sph gma' tsph cv in

        let* s' = check gma' s (ObjV scatv) in
        let* t' = check gma' t (ObjV tcatv) in

        let sv = eval tp lc s' in
        let tv = eval tp lc t' in

        let (bsphv) = ValuePdUtil.match_homs cv in

        let bdim = length bsphv in
        let sdim = length ssph' + bdim in
        let tdim = length tsph' + bdim in

        let* _ = Result.ok_if_true (sdim = tdim)
            ~error:(`PastingError "cylcoh source and target cells have different dims") in

            let k = length gma'.loc in
            let src_cat_vars = free_vars_val k scatv in
            let src_vars = free_vars_val k sv in
            let tgt_cat_vars = free_vars_val k tcatv in
            let tgt_vars = free_vars_val k tv in
            let pd_dim = Pd.dim_pd pd in

            if (sdim > pd_dim) then
              (* Coherence Case *)


              let pd_vars = Pd.fold_pd ipd fvs_empty
                  ~f:(fun vs i -> Set.add vs i) in
              let tot_src_vars = Set.union src_cat_vars src_vars in
              let tot_tgt_vars = Set.union tgt_cat_vars tgt_vars in

              if (not (Set.is_subset pd_vars ~of_:tot_src_vars) ||
                  not (Set.is_subset pd_vars ~of_:tot_tgt_vars)) then
                Error (`FullnessError "cylinder coherence case is not full")
              else Ok (gt,pd,c',(ssph',s'),(tsph',t'))

            else

              let pd_src = Pd.truncate true (pd_dim - 1) ipd in
              let pd_tgt = Pd.truncate false (pd_dim - 1) ipd in

              let pd_src_vars = Pd.fold_pd pd_src fvs_empty
                  ~f:(fun vs i -> Set.add vs i) in
              let pd_tgt_vars = Pd.fold_pd pd_tgt fvs_empty
                  ~f:(fun vs i -> Set.add vs i) in

              let tot_src_vars = Set.union src_cat_vars src_vars in
              let tot_tgt_vars = Set.union tgt_cat_vars tgt_vars in

              if (not (Set.is_subset pd_src_vars ~of_:tot_src_vars)) then
                Error (`FullnessError "non-full source")
              else if (not (Set.is_subset pd_tgt_vars ~of_:tot_tgt_vars)) then
                Error (`FullnessError "non-full target")
              else Ok (gt,pd,c',(ssph',s'),(tsph',t'))

    )

let rec check_defs gma defs =
  let module E = ExprUtil in
  match defs with
  | [] -> Ok gma
  | (TermDef (id,tl,ty,tm))::ds ->
    log_msg "----------------";
    log_msg (Fmt.str "Checking definition: %s" id);
    let (abs_ty,abs_tm) = E.abstract_tele_with_type tl ty tm in
    let* ty_tm = check gma abs_ty TypV in
    let ty_val = eval gma.top gma.loc ty_tm in
    let* tm_tm = check gma abs_tm ty_val in
    let tm_val = eval gma.top gma.loc tm_tm in
    log_msg (Fmt.str "Checking complete for %s" id);
    let tm_nf = term_to_expr Emp (quote true (gma.lvl) tm_val) in
    let ty_nf = term_to_expr Emp (quote true (gma.lvl) ty_val) in
    pr "Type: @[%a@]@," (pp_expr_gen ~tpd:ExprPdUtil.tele_to_name_pd ~si:false ~pc:true ~fh:true) ty_nf;
    pr "Term: @[%a@]@," (pp_expr_gen ~tpd:ExprPdUtil.tele_to_name_icit ~si:false ~pc:true ~fh:false) tm_nf;
    check_defs (define gma id tm_val ty_val) ds
  | (CohDef (id,g,c,s,t))::ds ->
    log_msg "----------------";
    log_msg (Fmt.str "Checking coherence: %s" id);
    let* (tl,pd,ct,st,tt) = check_coh gma g c s t in
    let coh_ty = eval gma.top gma.loc
                   (tele_to_pi tl (ObjT (HomT (ct,st,tt)))) in
    let coh_tm = eval gma.top gma.loc (CohT (pd,ct,st,tt)) in
    let coh_ty_nf = term_to_expr Emp (quote false gma.lvl coh_ty) in
    let coh_tm_nf = term_to_expr Emp (quote false gma.lvl coh_tm) in
    log_msg (Fmt.str "Coh type: @[%a@]" pp_expr coh_ty_nf);
    log_msg (Fmt.str "Coh expr: @[%a@]" pp_expr coh_tm_nf);
    check_defs (define gma id coh_tm coh_ty) ds
  | (Normalize (tl,tm))::ds ->
    log_msg "----------------";
    log_msg (Fmt.str "Normalizing: @[%a@]" pp_expr tm);
    let* _ = with_tele gma tl (fun gma' _ _ ->
        let* (tm',_) = infer gma' tm in
        let tm_val = eval gma'.top gma'.loc tm' in
        let tm_val_fix = fixup_impl tm_val in
        let tm_nf = quote true (gma'.lvl) tm_val_fix in
        let (tops,tm_nf_top) = top_levelify Emp tm_nf in
        let tm_expr = term_to_expr (names gma') tm_nf_top in
        let top_expr = map_suite tops ~f:(fun (x,nm) -> (nm, term_to_expr (names gma') x)) in
        let orig_nf = term_to_expr (names gma') tm_nf in
        log_val "Original Normal Form" orig_nf (pp_expr_gen ~tpd:ExprPdUtil.tele_to_name_icit ~si:false ~pc:true ~fh:false);
        let _ = map_suite top_expr ~f:(fun (nm,x) -> log_msg (Fmt.str "%s: %a" nm pp_expr x); ()) in
        log_val "Normal form" tm_expr pp_expr;
        log_val "Size" (expr_syntax_size orig_nf) int;
        Ok ()
      ) in
    check_defs gma ds
  | (Assert (tl, t1, t2))::ds ->
     log_msg "----------------";
     log_msg (Fmt.str "Asserting: @[%a@] = @[%a@]" pp_expr t1 pp_expr t2);
     let* _ = with_tele gma tl (fun gma' _ _ ->
       let* (t1',_) = infer gma' t1 in
       let* (t2',_) = infer gma' t2 in
       let t1_val = eval gma'.top gma'.loc t1' in
       let t2_val = eval gma'.top gma'.loc t2' in
       if is_same (gma'.lvl) t1_val t2_val then
         (log_msg "Assertion succeeded"; Ok ()) else
         Error (`AssertError (t1_val, t2_val))) in
     check_defs gma ds


let run_tc m =
  match m with
  | Ok _ ->
    Fmt.pr "@[<v>----------------@,Success!@,@,@]%!"
  | Error err ->
     Fmt.pr "@,Typing error: @,@,%a@,@,%!" pp_error err
end
