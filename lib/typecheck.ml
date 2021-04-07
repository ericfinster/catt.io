(*****************************************************************************)
(*                                                                           *)
(*                           Typechecking Routines                           *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
    
open Base
open Suite
open Expr
open Term
open Value 
open Meta
open Eval
open Unify
open Syntax
open Cylinder

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
  | `InvalidCylinder of string
  | `InternalError
]

let rec check gma expr typ = 
  (* let typ_tm = quote false gma.lvl typ in
   * let typ_expr = term_to_expr (names gma) typ_tm in 
   * pr "Checking @[%a@] has type @[%a@]@," pp_expr_with_impl expr pp_expr_with_impl typ_expr ; *)
  
  let switch e expected = 
    (* pr "switching mode@,";
     * pr "e: %a@," pp_expr e;
     * pr "exp: %a@," pp_term (quote gma.lvl expected false); *)
    let* (e',inferred) = insert gma (infer gma e) in
    try unify OneShot gma.top gma.lvl expected inferred ; Ok e'
    with Unify_error msg ->
      pr "Unification error: %s\n" msg;
      (* I guess the unification error will have more information .... *)
      let nms = names gma in 
      let inferred_nf = term_to_expr nms (quote false gma.lvl inferred) in
      let expected_nf = term_to_expr nms (quote true gma.lvl expected) in 
      let msg = String.concat [ str "@[<v>The expression: @,@, @[%a@]@,@,@]" pp_expr e; 
                                str "@[<v>has type: @,@,  @[%a@]@,@,@]" pp_expr inferred_nf; 
                                str "@[<v>but was expected to have type: @,@, @[%a@]@,@]"
                                 pp_expr expected_nf ]

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

  | (CylE (b,l,c) , ObjV cat) ->
    begin match value_to_cyl_typ cat with
     | Error _ -> switch expr (ObjV cat)
     | Ok (bc,ct) ->
       let module C = ValueCyl in

       let btyp = ObjV (C.sph_to_cat bc (base_sph ct)) in
       let ltyp = ObjV (C.sph_to_cat bc (lid_sph ct)) in

       (* pr "@[base typ: %a@]@," pp_value btyp;
        * pr "@[lid typ: %a@]@," pp_value ltyp; *)

       let* bt = check gma b btyp in
       let* lt = check gma l ltyp in

       let bv = eval gma.top gma.loc bt in 
       let lv = eval gma.top gma.loc lt in
       let ctyp = ObjV (C.sph_to_cat bc
                          (C.core_sph bc (Emp,to_list ct) bv lv)) in

       (* pr "@[core typ: %a@]@," pp_value ctyp; *)

       let* ct = check gma c ctyp in

       Ok (CylT (bt,lt,ct))
    end

  | (HoleE , _) -> (* pr "fresh meta@,"; *)
    let mv = fresh_meta () in Ok mv
  
  | (e, expected) -> switch e expected

and infer gma expr = 
  (* pr "@[<v>Inferring type of: @[%a@]@,@]"
   *   pp_expr_with_impl expr ; *)
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
    (* pr "@[<v>Generated ucomp: @[%a]@,@]" pp_expr e; *)
    let* (_,ty) = infer gma e in
    (* pr "@[<b>Result of inferrence: @[%a]@,@]" pp_term tm; *)
    Ok (UCompT (UnitPd pd),ty)

  | UCompE (DimSeq ds) ->
    let pd = Pd.comp_seq ds in
    let e = expr_ucomp pd in
    (* pr "@[<v>Generated ucomp: @[%a]@,@]" pp_expr e; *)
    let* (_,ty) = infer gma e in 
    Ok (UCompT (DimSeq ds),ty)

  | CylCohE _ -> Error (`NotImplemented "cylcoh")
                   
  | CohE (g,c,s,t) ->
    let* (tl,cn,pd,ct,st,tt) = check_coh gma g c s t in
    let coh_ty = eval gma.top gma.loc
        (tele_to_pi tl (ObjT (HomT (ct,st,tt)))) in
    (* let ty_nf = term_to_expr Emp (quote false gma.lvl coh_ty) in 
     * pr "@[<v>Coherence: @[%a@]@,inferred to have type: @[%a@]@,@]"
     *   pp_expr_with_impl (CohE (g,c,s,t)) pp_expr_with_impl ty_nf; *)
    Ok (CohT (cn,pd,ct,st,tt) , coh_ty) 

  | CylE (b,l,c) ->
    (* This could be much smarter.  By deconstructing the 
       types of the various components, we could have tighter
       constraints for unification ... *)
    let* (btm,_) = infer gma b in
    let* (ltm,_) = infer gma l in
    let* (ctm,_) = infer gma c in
    let m = eval gma.top gma.loc (fresh_meta ()) in
    Ok (CylT (btm,ltm,ctm), m)
      
  | BaseE cyl ->
    let* (cyl_tm,cyl_typ) = infer gma cyl in
    let btm = BaseT cyl_tm in
    
    (match force_meta cyl_typ with
     | ObjV cat ->
       (match value_to_cyl_typ cat with
        | Error _ -> Ok (btm,obj_meta gma cyl_typ)
        | Ok (bc,ct) ->
          let module C = ValueCyl in
          let btyp = ObjV (C.sph_to_cat bc (base_sph ct)) in
          (* pr "@[inferred base typ: %a@]@," pp_value btyp; *)
          Ok (btm,btyp))
     | _ -> Ok (btm,obj_meta gma cyl_typ))

  | LidE cyl ->
    let* (cyl_tm,cyl_typ) = infer gma cyl in
    let ltm = LidT cyl_tm in
    
    (match force_meta cyl_typ with
     | ObjV cat ->
       (match value_to_cyl_typ cat with
        | Error _ -> Ok (ltm,obj_meta gma cyl_typ)
        | Ok (bc,ct) ->
          let module C = ValueCyl in
          let ltyp = ObjV (C.sph_to_cat bc (lid_sph ct)) in
          (* pr "@[inferred lid typ: %a@]@," pp_value ltyp; *)
          Ok (ltm,ltyp))
     | _ -> Ok (ltm,obj_meta gma cyl_typ))

  | CoreE cyl -> 
    let* (cyl_tm,cyl_typ) = infer gma cyl in
    let cyl_val = eval gma.top gma.loc cyl_tm in 
    let ctm = CoreT cyl_tm in
    begin match force_meta cyl_typ with
     | ObjV cat ->
       (match value_to_cyl_typ cat with
        | Error _ -> Ok (ctm,obj_meta gma cyl_typ)
        | Ok (bc,ct) ->
          let module C = ValueCyl in
          let ctyp = ObjV (C.sph_to_cat bc
                             (C.core_sph bc (Emp,to_list ct)
                             (baseV cyl_val) (lidV cyl_val))) in
          (* pr "@[inferred core typ: %a@]@," pp_value ctyp; *)
          Ok (ctm,ctyp))
       
     | _ -> Ok (ctm,obj_meta gma cyl_typ)
    end

  | ArrE c -> 
    let* c' = check gma c CatV in
    Ok (ArrT c' , CatV)
      
  | CatE -> Ok (CatT , TypV)
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
  (* pr "@[<v>check_coh@,gma: @[%a@]@,c: @[%a@]@,s: @[%a@]@,t: @[%a@]@,@]"
   *   (pp_tele pp_expr) g pp_expr c pp_expr s pp_expr t; *)
  with_tele (empty_loc gma) g (fun gma' gv tl ->

      (* pr "@[<v>gv: @[%a@]@,@]" (pp_tele pp_value) gv; *)
      
      match ValuePdUtil.tele_to_pd gv with
      | Error msg -> Error (`PastingError msg)
      | Ok (cn,pd) ->

        (* pr "@[<v>cn: %a@,pd: %a@,@]" (pair string pp_ict) cn
         *   (Pd.pp_pd (pair string pp_ict)) pd; *)
          
        let lc = gma'.loc in
        let tp = gma'.top in

        let cat_idx = length gv - 1 in
        let ipd = idx_pd pd in 
          
        let* c' = check gma' c CatV in
        let cv = eval tp lc c' in
        
        (* pr "@[<v>About to check src and tgt@,cv: %a@,@]" pp_value (force_meta cv); *)
        let* s' = check gma' s (ObjV cv) in
        let* t' = check gma' t (ObjV cv) in
        
        (* pr "@[<v>source: %a@,@]" pp_term s';
         * pr "@[<v>target: %a@,@]" pp_term t'; *)

        let sv = eval tp lc s' in 
        let tv = eval tp lc t' in 
        
        (* pr "@[<v>cv: %a@,@]" pp_value (force_meta cv); *)
        
        let (bc,sph) = ValuePdUtil.match_homs cv in 

        (* pr "@[<v>bc: %a@,@]" pp_value bc; *)
        
        (* We force the underlying category to be a variable ... *)
        begin try unify OneShot gma'.top gma'.lvl (varV 0) bc ;

            
            let k = length gma'.loc in 
            let cat_vars = free_vars_val k cv in
            let src_vars = free_vars_val k sv in
            let tgt_vars = free_vars_val k tv in
            let pd_dim = Pd.dim_pd pd in 

            if (length sph + 1 > pd_dim) then
              (* Coherence Case *)

              let pd_vars = Pd.fold_pd ipd (fvs_singleton cat_idx)
                  ~f:(fun vs i -> Set.add vs i) in 
              let tot_src_vars = Set.union cat_vars src_vars in
              let tot_tgt_vars = Set.union cat_vars tgt_vars in 
              if (not (Set.is_subset pd_vars ~of_:tot_src_vars) ||
                  not (Set.is_subset pd_vars ~of_:tot_tgt_vars)) then
                Error (`FullnessError "coherence case is not full")                 
              else Ok (tl,cn,pd,c',s',t')
          
            else

              let pd_src = Pd.truncate true (pd_dim - 1) ipd in
              let pd_tgt = Pd.truncate false (pd_dim - 1) ipd in

              let pd_src_vars = Pd.fold_pd pd_src (fvs_singleton cat_idx)
                  ~f:(fun vs i -> Set.add vs i) in 
              let pd_tgt_vars = Pd.fold_pd pd_tgt (fvs_singleton cat_idx)
                  ~f:(fun vs i -> Set.add vs i) in

              let tot_src_vars = Set.union cat_vars src_vars in
              let tot_tgt_vars = Set.union cat_vars tgt_vars in

              if (not (Set.is_subset pd_src_vars ~of_:tot_src_vars)) then
                Error (`FullnessError "non-full source")
              else if (not (Set.is_subset pd_tgt_vars ~of_:tot_tgt_vars)) then
                Error (`FullnessError "non-full target")
              else Ok (tl,cn,pd,c',s',t')

          with Unify_error _ -> Error (`FullnessError "invalid base category") end 

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
      | Ok (cn,pd) ->
          
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
        
        let (bc,bsphv) = ValuePdUtil.match_homs cv in 

        let bdim = length bsphv in 
        let sdim = length ssph' + bdim in
        let tdim = length tsph' + bdim in

        let* _ = Result.ok_if_true (sdim = tdim)
            ~error:(`PastingError "cylcoh source and target cells have different dims") in 
        
        begin try unify OneShot gma'.top gma'.lvl (varV 0) bc ;

            let k = length gma'.loc in 
            let src_cat_vars = free_vars_val k scatv in
            let src_vars = free_vars_val k sv in
            let tgt_cat_vars = free_vars_val k tcatv in 
            let tgt_vars = free_vars_val k tv in
            let pd_dim = Pd.dim_pd pd in 

            if (sdim > pd_dim) then
              (* Coherence Case *)


              let pd_vars = Pd.fold_pd ipd (fvs_singleton cat_idx)
                  ~f:(fun vs i -> Set.add vs i) in 
              let tot_src_vars = Set.union src_cat_vars src_vars in
              let tot_tgt_vars = Set.union tgt_cat_vars tgt_vars in 

              if (not (Set.is_subset pd_vars ~of_:tot_src_vars) ||
                  not (Set.is_subset pd_vars ~of_:tot_tgt_vars)) then
                Error (`FullnessError "cylinder coherence case is not full")                 
              else Ok (gt,cn,pd,c',(ssph',s'),(tsph',t'))
          
            else

              let pd_src = Pd.truncate true (pd_dim - 1) ipd in
              let pd_tgt = Pd.truncate false (pd_dim - 1) ipd in

              
              let pd_src_vars = Pd.fold_pd pd_src (fvs_singleton cat_idx)
                  ~f:(fun vs i -> Set.add vs i) in 
              let pd_tgt_vars = Pd.fold_pd pd_tgt (fvs_singleton cat_idx)
                  ~f:(fun vs i -> Set.add vs i) in

              let tot_src_vars = Set.union src_cat_vars src_vars in
              let tot_tgt_vars = Set.union tgt_cat_vars tgt_vars in

              if (not (Set.is_subset pd_src_vars ~of_:tot_src_vars)) then
                Error (`FullnessError "non-full source")
              else if (not (Set.is_subset pd_tgt_vars ~of_:tot_tgt_vars)) then
                Error (`FullnessError "non-full target")
              else Ok (gt,cn,pd,c',(ssph',s'),(tsph',t'))

          with Unify_error _ -> Error (`FullnessError "invalid base category") end 

    )

let rec check_defs gma defs =
  let module E = ExprUtil in 
  match defs with
  | [] -> Ok gma
  | (TermDef (id,tl,ty,tm))::ds ->
    pr "----------------@,";
    pr "Checking definition: %s@," id;
    let (abs_ty,abs_tm) = E.abstract_tele_with_type tl ty tm in
    let* ty_tm = check gma abs_ty TypV in
    let ty_val = eval gma.top gma.loc ty_tm in
    let* tm_tm = check gma abs_tm ty_val in
    let tm_val = eval gma.top gma.loc tm_tm in 
    pr "Checking complete for %s@," id;
    (* let tm_nf = term_to_expr Emp (quote (gma.lvl) tm_val false) in
     * let ty_nf = term_to_expr Emp (quote (gma.lvl) ty_val false) in *)
    (* pr "Type: @[%a@]@," pp_expr ty_nf; *)
    (* pr "Term: @[%a@]@," pp_expr tm_nf; *)
    check_defs (define gma id tm_val ty_val) ds
  | (CohDef (id,g,c,s,t))::ds ->
    pr "----------------@,";
    pr "Checking coherence: %s@," id;
    let* (tl,cn,pd,ct,st,tt) = check_coh gma g c s t in
    let coh_ty = eval gma.top gma.loc
        (tele_to_pi tl (ObjT (HomT (ct,st,tt)))) in
    let coh_tm = eval gma.top gma.loc (CohT (cn,pd,ct,st,tt)) in
    let coh_ty_nf = term_to_expr Emp (quote false gma.lvl coh_ty) in
    let coh_tm_nf = term_to_expr Emp (quote false gma.lvl coh_tm) in
    pr "@[<v>Coh type: @[%a@]@,@]" pp_expr coh_ty_nf;
    (* pr "@[<v>Coh term: @[%a@]@,@]" pp_term (CohT (cn,pd,ct,st,tt)); *)
    pr "@[<v>Coh expr: @[%a@]@,@]" pp_expr coh_tm_nf;
    check_defs (define gma id coh_tm coh_ty) ds
  | (CylCohDef (id,g,c,s,t))::ds ->
    pr "----------------@,";
    pr "Checking cylinder coherence: %s@," id;
    let* (_,cn,pd,ct,(ssph,s),(tsph,t)) = check_cyl_coh gma g c s t in
    (* pr "@[<v>ct: @[%a@]@,sdsc: @[%a@]@,tdsc: @[%a@]@,@]"
     *   pp_term ct (Pd.pp_disc pp_term) (ssph,s) (Pd.pp_disc pp_term) (tsph,t); *)
    let cctt = TermCylCoh.cyl_coh_typ cn pd ct (ssph,s) (tsph,t) in
    (* pr "cylinder type: %a@," pp_expr (term_to_expr Emp cctt); *)
    let cyl_ctm = eval gma.top gma.loc
        (CylCohT (cn,pd,ct,(ssph,s),(tsph,t))) in 
    let cyl_cty = eval gma.top gma.loc cctt in 
    let cyl_cty_nf = term_to_expr Emp (quote false gma.lvl cyl_cty) in 
    let cyl_nf = term_to_expr Emp (quote false gma.lvl cyl_ctm) in
    pr "@[<v>Cylcoh type: @[%a@]@,@]" pp_expr cyl_cty_nf;
    pr "@[<v>Cylcoh expr: @[%a@]@,@]" pp_expr cyl_nf;
    let* _ = check gma cyl_nf cyl_cty in
    pr "@[<v>Rechecking succeeded!@,@]";
    check_defs (define gma id cyl_ctm cyl_cty) ds
     
