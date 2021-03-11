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
(*                           Context/Pd Conversion                           *)
(*****************************************************************************)

let rec underlying_cat v =
  match v with
  | HomV (c,_,_) ->
    let (cat,dim) = underlying_cat c in
    (cat,dim+1)
  | _ -> (v,0)

let rec nth_tgt i ty tm =
  if (i = 0) then Ok (ty, tm) else
    match ty with
    | HomV (c,_,t) ->
      nth_tgt (i-1) c t
    | _ -> Error "No target"

let unobj v =
  match v with
  | ObjV v' -> Ok v'
  | _ -> Error (str "Not a type of objects: %a" pp_value v)

(* Hmmm.  We are hard-coded to be in the empty context here .... *)
let ctx_to_pd i loc = 
  let rec go l loc =
    (* pr "Trying pasting context: @[<hov>%a@]@," (pp_suite pp_value) loc; *)
    match loc with
    | Emp -> Error "Empty context is not a pasting diagram"
    | Ext(Emp,_) -> Error "Singleton context is not a pasting diagram"
    | Ext(Ext(Emp,CatV),ObjV (RigidV (i',EmpSp))) ->
      if (i = i') then 
        Ok (Pd.Br (l,Emp),varV i,varV (i+1),i+2,0)
      else Error "Wrong base category for object"
    | Ext(Ext(loc',tobj),fobj) ->

      (* pr "tobj: %a@," pp_value tobj;
       * pr "fobj: %a@," pp_value fobj; *)
      
      let* tty = unobj tobj in
      let* fty = unobj fobj in

      let* (pd,sty,stm,k,dim) = go (l+2) loc' in
      let (_,tdim) = underlying_cat tty in
      let codim = dim - tdim in
      let* (sty',stm') = nth_tgt codim sty stm in

      if (Poly.(<>) sty' tty) then

        let msg = str 
            "@[<v>Source and target types incompatible.
                  @,Source: %a
                  @,Target: %a@]"
            pp_value sty' pp_value tty
        in Error msg

      else let ety = HomV (sty',stm',varV k) in
        if (Poly.(<>) ety fty) then 

          let msg = str
              "@[<v>Incorrect filling type.
                    @,Expected: %a
                    @,Provided: %a@]"
              pp_value ety
              pp_value fty
          in Error msg

        else let* pd' = Pd.insert_right pd tdim (l+1)
                 (Pd.Br (l, Emp)) in
          Ok (pd', fty, varV (k+1), k+2, tdim+1)
  in go 0 loc

(*****************************************************************************)
(*                                   Debug                                   *)
(*****************************************************************************)

let rec quote_types ufld typs =
  match typs with
  | Emp -> (Emp,0)
  | Ext (typs', (nm, (Defined,typ))) ->
    let (res_typs, l) = quote_types ufld typs' in
    let typ_tm = quote l typ ufld in
    (Ext (res_typs,(nm,typ_tm)),l)
  | Ext (typs', (nm, (_,typ))) ->
    let (res_typs, l) = quote_types ufld typs' in
    let typ_tm = quote l typ ufld in
    (Ext (res_typs,(nm, typ_tm)),l+1)
    
let dump_ctx ufld gma =
  let (tl,_) = quote_types ufld gma.types in 
  pr "Context: @[<hov>%a@]@,"
    (pp_suite (parens (pair ~sep:(any " : ") string pp_term))) tl

(*****************************************************************************)
(*                               Free Variables                              *)
(*****************************************************************************)

let fvs_empty = Set.empty (module Int)
let fvs_singleton k = Set.singleton (module Int) k
    
let rec free_vars k tm =
  match tm with
  | VarT i when i >= k -> fvs_singleton i 
  | VarT _ -> fvs_empty
  | TopT _ -> fvs_empty
  | LamT (_,_,bdy) -> free_vars (k+1) bdy
  | AppT (u,v,_) ->
    Set.union (free_vars k u) (free_vars k v)
  | PiT (_,_,a,b) ->
    Set.union (free_vars k a) (free_vars (k+1) b)
  (* This could be more complicated later on  *)
  | QuotT (_,_) -> fvs_empty
  | ObjT c -> free_vars k c
  | HomT (c,s,t) ->
    Set.union (free_vars k c) (Set.union (free_vars k s) (free_vars k t))
  | CohT (g,a) ->
    let rec go k g =
      match g with
      | Emp -> free_vars k a
      | Ext (g',_) -> go (k+1) g'
    in go k g
  | CylT (b,l,c) ->
    Set.union (free_vars k b) (Set.union (free_vars k l) (free_vars k c))
  | BaseT c -> free_vars k c
  | LidT c -> free_vars k c
  | CoreT c -> free_vars k c
  | ArrT c -> free_vars k c
  | CatT -> fvs_empty
  | TypT -> fvs_empty
  | MetaT _ -> fvs_empty
  | InsMetaT _ -> fvs_empty

let rec free_vars_val k v =
  let fvc x = free_vars_val k x in 
  let sp_vars sp = free_vars_sp k sp in 
  match force_meta v with
  | FlexV (_,sp) -> sp_vars sp
  | RigidV (l,sp) -> Set.add (sp_vars sp) (lvl_to_idx k l) 
  | TopV (_,sp,_) -> sp_vars sp
  | LamV (_,_,Closure (_,loc,tm)) -> free_vars (length loc) tm
  | PiV (_,_,a,Closure (_,loc,b)) ->
    Set.union (free_vars_val k a) (free_vars (length loc) b)
  | QuotV (_,sp,_) -> sp_vars sp 
  | ObjV c -> free_vars_val k c
  | HomV (c,s,t) ->
    Set.union_list (module Int) [fvc c; fvc s; fvc t]
  | CohV (v,sp) ->
    Set.union (free_vars_val k v) (sp_vars sp)
  | CylV (b,l,c) ->
    Set.union_list (module Int) [fvc b; fvc l; fvc c]
  | ArrV c -> fvc c
  | CatV -> fvs_empty
  | TypV -> fvs_empty 

and free_vars_sp k sp =
  let fvc x = free_vars_val k x in 
  let fvcs x = free_vars_sp k x in 
  match sp with
  | EmpSp -> fvs_empty
  | AppSp (sp',u,_) ->
    Set.union (fvcs sp') (fvc u)
  | BaseSp sp' -> fvcs sp'
  | LidSp sp' -> fvcs sp'
  | CoreSp sp' -> fvcs sp'

(*****************************************************************************)
(*                                 Cylinders                                 *)
(*****************************************************************************)

let rec base_type cat =
  match cat with
  | ArrV c -> Ok c
  | HomV (cat',s,t) ->
    let* bc = base_type cat' in
    Ok (HomV (bc, baseV s, baseV t))
  | _ -> Error `InternalError

let rec lid_type cat =
  match cat with 
  | ArrV c -> Ok c
  | HomV (cat',s,t) ->
    let* bc = lid_type cat' in
    Ok (HomV (bc, lidV s, lidV t))
  | _ -> Error `InternalError

(* let rec core_type base lid cat =
 *   match cat with
 *   | ArrV c -> Ok (HomV (c, base, lid))
 *   | HomV (_, _, _) ->
 *     let* pd = Pd.comp_seq [2;1;2] in
 *     let _ = unbiased_comp pd in
 *     
 *     (\* Here, s and t are supposed to themselves be cylinders. *\)
 *     Error "blorp"
 *   | _ -> Error "double blorp" *)

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
]

let rec check gma expr typ = 
  (* let typ_tm = quote gma.lvl typ false in
   * let typ_expr = term_to_expr (names gma) typ_tm in 
   * pr "Checking %a has type %a@," pp_expr_with_impl expr pp_expr_with_impl typ_expr ; *)
  (* dump_ctx true gma; *)
  match (expr, force_meta typ) with
  
  | (e , TopV (_,_,tv)) ->
    check gma e tv
  
  | (LamE (nm,i,e) , PiV (_,i',a,b)) when Poly.(=) i i' ->
    (* pr "canonical lambda@,"; *)
    let* bdy = check (bind gma nm a) e (b $$ varV gma.lvl) in
    Ok (LamT (nm,i,bdy))
  
  | (t , PiV (nm,Impl,a,b)) ->
    (* pr "non-canonical lambda@,"; *)
    let* bdy = check (bind gma nm a) t (b $$ varV gma.lvl) in
    Ok (LamT (nm,Impl,bdy))

  | (CylE (b,l,c) , ObjV cat) ->

    let* b_typ = base_type cat in 
    let* b' = check gma b b_typ in
    let bv = eval gma.top gma.loc b' in
    let* l_typ = lid_type cat in 
    let* l' = check gma l l_typ in
    let lv = eval gma.top gma.loc l' in
    (* And now, the harder one .... *)
    let* c' = check gma c (ObjV (HomV (cat,bv,lv))) in
    Ok (CylT (b',l',c'))

  | (HoleE , _) -> (* pr "fresh meta@,"; *)
    let mv = fresh_meta () in Ok mv
  
  | (e, expected) -> 
    (* pr "switching mode@,";
     * pr "e: %a@," pp_expr e;
     * pr "exp: %a@," pp_term (quote gma.lvl expected false); *)
    let* (e',inferred) = insert gma (infer gma e) in
    try unify OneShot gma.top gma.lvl expected inferred ; Ok e'
    with Unify_error _ ->
      let nms = names gma in 
      let inferred_nf = term_to_expr nms (quote gma.lvl inferred false) in
      let expected_nf = term_to_expr nms (quote gma.lvl expected false) in 
      let msg = str "@[<v>Type mismatch:@,Expression: %a@,Expected: %a@,Inferred: %a@,@]"
          pp_expr e pp_expr expected_nf pp_expr inferred_nf
      in Error (`TypeMismatch msg) 

and infer gma expr = 
  (* pr "Inferring type of %a@," pp_expr expr ;
   * dump_ctx true gma; *)
  match expr with
  
  | VarE nm -> (
      try
        let (idx,(b,typ)) = assoc_with_idx nm gma.types in
        match b with
        | Bound ->
          (* pr "Inferred variable of index %d to have type: %a@," idx pp_term (quote gma.lvl typ true) ; *)
          Ok (VarT idx, typ)
        | Defined ->
          (* pr "Inferred definition %s to have type: %a@," nm pp_term (quote gma.lvl typ true) ; *)
          Ok (TopT nm, typ)
      with Lookup_error -> Error (`NameNotInScope nm)
    )
  
  | LamE (nm,ict,e) ->
    let a = eval gma.top gma.loc (fresh_meta ()) in
    let* (e', t) = insert gma (infer (bind gma nm a) e) in
    Ok (LamT (nm,ict,e') , PiV (nm,ict,a,Closure (gma.top,gma.loc,quote (gma.lvl + 1) t false)))
  
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

  | CohE (g,a) ->
    (* pr "Inferring a coherence: @[<hov>%a@]@," pp_expr (CohE (g,a)); *)
    let* (gt,at) = check_coh gma g a in
    let coh_ty = eval gma.top gma.loc (tele_to_pi gt (ObjT at)) in
    (* pr "Finished with coherence: @[<hov>%a@]@," pp_expr (CohE (g,a)); *)
    Ok (CohT (gt,at) , coh_ty)

  | CylE (_,_,_) -> Error (`NotImplemented "Infer CylE")
  | BaseE _ -> Error (`NotImplemented "Infer BaseE")
  | LidE _ -> Error (`NotImplemented "Infer LidE")
  | CoreE _ -> Error (`NotImplemented "Infer CoreE")

  | ArrE c -> 
    let* c' = check gma c CatV in
    Ok (ArrT c' , CatV)
      
  | CatE -> Ok (CatT , TypV)
  | TypE -> Ok (TypT , TypV)

  (* You need to grab the return here and give back the meta term
     so that you don't unfold automatically ... *)
  | QuotE (PComp pd) ->
    (* pr "inferring a pasting composite: %a@," Pd.pp_tr pd; *)
    let e = unbiased_comp_expr pd in
    (* pr "expr: @[<hov>%a@]@," pp_expr_with_impl e;  *)
    let* (t,typ) = infer gma e in
    Ok (QuotT (PComp pd, t), typ)

  | QuotE (SComp ds) ->
    (match Pd.comp_seq ds with
     | Ok pd ->
       let* (t,typ) = infer gma (unbiased_comp_expr pd) in
       Ok (QuotT (SComp ds,t),typ)
     | Error _ -> Error (`BadCohQuot "invalid comp sequence"))

  | HoleE ->
    let a = eval gma.top gma.loc (fresh_meta ()) in
    let t = fresh_meta () in
    Ok (t , a)

and with_tele gma tl m =
  match tl with
  | Emp -> m gma Emp Emp
  | Ext (tl',(id,ict,ty)) ->
    with_tele gma tl' (fun g tv tt ->
        let* ty_tm = check g ty TypV in
        let ty_val = eval g.top g.loc ty_tm in 
        m (bind g id ty_val)
          (Ext (tv,ty_val))
          (Ext (tt,(id,ict,ty_tm))))

and check_coh gma g a =
  with_tele gma g (fun gma' gv gt ->
      match ctx_to_pd (length gma.loc) gv with
      | Ok (pd,_,_,_,_) ->
        
        (* pr "Valid pasting context!@,";
         * pr "Going to check return type: @[%a@]@," pp_expr a; *)
        let* a' = check gma' a CatV in
        (* pr "return type: %a@," pp_term a'; *)
        let av = eval gma'.top gma'.loc a' in 
        let (ucat,bdim) = underlying_cat av in
        let cat_lvl = (length gma'.loc) - (length gv) in
        let cat_idx = length gv - 1 in 
        (* pr "cat_lvl: %d@," cat_lvl; *)
        (try unify OneShot gma'.top gma'.lvl (varV cat_lvl) ucat;
           
           (match av with
            | HomV (c,s,t) ->

              let k = length gma'.loc in 
              let cat_vars = free_vars_val k c in
              let src_vars = free_vars_val k s in
              let tgt_vars = free_vars_val k t in
              let pd_dim = Pd.dim_pd pd in 

              (* pr "bdim: %d@," bdim;
               * pr "pd_dim: %d@," pd_dim;
               * pr "cat_vars: @[%a@]@," (list ~sep:(any ", ") int) (Set.to_list cat_vars);
               * pr "src_vars: @[%a@]@," (list ~sep:(any ", ") int) (Set.to_list src_vars);
               * pr "tgt_vars: @[%a@]@," (list ~sep:(any ", ") int) (Set.to_list tgt_vars); *)

              if (bdim > pd_dim) then

                let pd_vars = Set.of_list (module Int) (cat_idx::to_list (Pd.labels pd)) in
                let tot_vars = Set.union cat_vars (Set.union src_vars tgt_vars) in

                (* pr "cat_idx: %d@," cat_idx;
                 * pr "pd_vars: @[<hov>%a@]@," (list ~sep:(any ", ") int) (Set.to_list pd_vars);
                 * pr "tot_vars: @[<hov>%a@]@," (list ~sep:(any ", ") int) (Set.to_list tot_vars); *)
                
                if (not (Set.is_subset pd_vars ~of_:tot_vars)) then
                  Error (`FullnessError "coherence case is not full")                 
                else Ok (gt,a')

              else

                let pd_src = Pd.truncate true (pd_dim - 1) pd in
                let pd_tgt = Pd.truncate false (pd_dim - 1) pd in

                let pd_src_vars = Set.of_list (module Int) (cat_idx::to_list (Pd.labels pd_src)) in
                let pd_tgt_vars = Set.of_list (module Int) (cat_idx::to_list (Pd.labels pd_tgt)) in

                let tot_src_vars = Set.union cat_vars src_vars in
                let tot_tgt_vars = Set.union cat_vars tgt_vars in

                if (not (Set.is_subset pd_src_vars ~of_:tot_src_vars)) then
                  Error (`FullnessError "non-full source")
                else if (not (Set.is_subset pd_tgt_vars ~of_:tot_tgt_vars)) then
                  Error (`FullnessError "non-full target")
                else Ok (gt,a')

            | _ -> Error (`FullnessError "invalid coherence return type"))


         with Unify_error _ -> Error (`FullnessError "invalid base category"))

      | Error msg -> Error (`PastingError msg))


let rec abstract_tele_with_tm tl ty tm =
  match tl with
  | Emp -> (ty,tm)
  | Ext (tl',(nm,ict,expr)) ->
    abstract_tele_with_tm tl'
      (PiE (nm,ict,expr,ty)) (LamE (nm,ict,tm))
              
let rec check_defs gma defs =
  match defs with
  | [] -> additional_tests () ; Ok gma
  | (TermDef (id,tl,ty,tm))::ds ->
    pr "----------------@,";
    pr "Checking definition: %s@," id;
    let (abs_ty,abs_tm) = abstract_tele_with_tm tl ty tm in
    let* ty_tm = check gma abs_ty TypV in
    let ty_val = eval gma.top gma.loc ty_tm in
    let* tm_tm = check gma abs_tm ty_val in
    let tm_val = eval gma.top gma.loc tm_tm in 
    pr "Checking complete for %s@," id;
    let tm_nf = term_to_expr Emp (quote (gma.lvl) tm_val false) in
    let ty_nf = term_to_expr Emp (quote (gma.lvl) ty_val false) in
    pr "Type: @[<hov>%a@]@," pp_expr ty_nf;
    pr "Term: @[<hov>%a@]@," pp_expr tm_nf;
    check_defs (define gma id tm_val ty_val) ds
  | (CohDef (id,g,a))::ds ->
    pr "----------------@,";
    pr "Checking coherence: %s@," id;
    let* (gt,at) = check_coh gma g a in
    let coh_ty = eval gma.top gma.loc (tele_to_pi gt (ObjT at)) in
    let coh_tm = eval gma.top gma.loc (CohT (gt , at)) in
    (* let coh_ty_nf = term_to_expr Emp (quote gma.lvl coh_ty false) in *)
    let coh_tm_nf = term_to_expr Emp (quote gma.lvl coh_tm false) in
    (* pr "Coh type: @[<hov>%a@]@," pp_expr coh_ty_nf; *)
    (* pr "Coh term raw: %a@," pp_term (CohT (gt,at));
     * pr "Coh term val: %a@," pp_value coh_tm;
     * pr "Coh term nf: %a@," pp_term (quote gma.lvl coh_tm false); *)
    pr "Coh expr: @[<hov>%a@]@," pp_expr coh_tm_nf;
    check_defs (define gma id coh_tm coh_ty) ds

and additional_tests _ =
  let _ = Int.of_string "45" in ()
  (* pr "----------------@,";
   * let s = [3;0;3] in 
   * match Pd.comp_seq s with
   * | Ok pd ->
   *   let pd_lvl = pd_to_lvl pd in 
   *   let pd_idx = pd_to_idx pd in
   *   let nms = map_suite (Pd.labels pd_lvl) ~f:(fun i -> str "x%a" pp_term i) in
   *   let utm = unbiased_comp pd_idx (VarT (length nms)) in 
   *   let uexp = term_to_expr (append (singleton "C") nms) utm in
   *   (\* pr "%a\n" pp_term utm; *\)
   *   pr "ucomp: @[<hov>%a@]@," pp_expr uexp
   * | Error s -> pr "error: %s" s *)

