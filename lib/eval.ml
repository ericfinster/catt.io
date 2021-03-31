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
  | AppT (u,v,ict) -> appV (eval top loc u) (eval top loc v) ict
  | PiT (nm,ict,u,v) -> PiV (nm, ict, eval top loc u, Closure (top,loc,v))
  | ObjT c -> ObjV (eval top loc c)
  | HomT (c,s,t) ->
    HomV (eval top loc c, eval top loc s, eval top loc t)

  | CylCohT _ -> failwith "eval cylcoh"
    (* let ctm = TermCylCoh.cylcoh g c s t in 
     * eval top loc (TermUtil.abstract_tele g ctm) *)

  | UCompT uc ->
    let v = eval top loc (term_ucomp_desc uc) in
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

and appV t u ict =
  match t with
  | FlexV (m,sp) -> FlexV (m,AppSp(sp,u,ict))
  | RigidV (i,sp) -> RigidV (i,AppSp(sp,u,ict))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u,ict),appV tv u ict)
  (* | CohV (v,sp) -> CohV (v,AppSp(sp,u,ict)) *)
  | LamV (_,_,cl) -> cl $$ u
  | UCompV (ucd,cohv,sp) -> UCompV (ucd,cohv,AppSp(sp,u,ict))
  | CohV (cn,pd,sph,s,t,sp) ->
    CohV (cn,pd,sph,s,t,AppSp(sp,u,ict))
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

and baseV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,BaseSp sp)
  | RigidV (i,sp) -> RigidV (i,BaseSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,BaseSp sp, baseV tv)
  (* | CohV (ga,sp) -> CohV (ga,BaseSp sp) *)
  | CylV (b,_,_) -> b 
  | UCompV (ucd,cohv,sp) -> UCompV (ucd,cohv,BaseSp sp)
  | CohV (cn,pd,sph,s,t,sp) ->
    CohV (cn,pd,sph,s,t,BaseSp sp)
  | _ -> raise (Eval_error "malformed base projection")

and lidV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,LidSp sp)
  | RigidV (i,sp) -> RigidV (i,LidSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,LidSp sp, lidV tv)
  (* | CohV (ga,sp) -> CohV (ga,LidSp sp) *)
  | CylV (_,l,_) -> l
  | UCompV (ucd,cohv,sp) -> UCompV (ucd,cohv,LidSp sp)
  | CohV (cn,pd,sph,s,t,sp) ->
    CohV (cn,pd,sph,s,t,LidSp sp)
  | _ -> raise (Eval_error "malformed lid projection")

and coreV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,CoreSp sp)
  | RigidV (i,sp) -> RigidV (i,CoreSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,CoreSp sp, coreV tv)
  (* | CohV (ga,sp) -> CohV (ga,CoreSp sp) *)
  | CylV (_,_,c) -> c
  | UCompV (ucd,cohv,sp) -> UCompV (ucd,cohv,CoreSp sp)
  | CohV (cn,pd,sph,s,t,sp) ->
    CohV (cn,pd,sph,s,t,CoreSp sp)
  | _ -> raise (Eval_error "malformed core projection")

and appLocV loc v =
  match loc with
  | Emp -> v
  | Ext (loc',u) -> appV (appLocV loc' v) u Expl

let rec runSpV v sp =
  match sp with
  | EmpSp -> v
  | AppSp (sp',u,ict) -> appV (runSpV v sp') u ict
  | BaseSp sp' -> baseV (runSpV v sp')
  | LidSp sp' -> lidV (runSpV v sp')
  | CoreSp sp' -> coreV (runSpV v sp')

let rec force_meta v =
  match v with
  | FlexV (m,sp) ->
    (match lookup_meta m with
     | Unsolved -> FlexV (m,sp)
     | Solved v -> force_meta (runSpV v sp))
  | _ -> v

let rec appArgs v args =
  match args with
  | Emp -> v
  | Ext (args',(ict,arg)) ->
    appV (appArgs v args') arg ict

(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

let rec quote ufld k v =
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

  | UCompV (_,cohv,sp) when ufld ->
    qcs (quote ufld k cohv) sp 
  | UCompV (uc,_,sp) -> qcs (UCompT uc) sp
  (* | CohV (v,sp) ->
   * 
   *   let pi_tm = quote ufld k v in
   *   let (g,a) = pi_to_tele pi_tm in
   *   (match a with
   *    | HomT (c,s,t) -> qcs (CohT (g,c,s,t)) sp
   *    | _ -> failwith "invalid coherence return type") *)
                        
  | CohV (cn,pd,c,s,t,sp) ->

    let k' = length (Pd.labels pd) + 1 in 
    let c' = quote ufld k' c in 
    let s' = quote ufld k' s in
    let t' = quote ufld k' t in 

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
  (* | CohV (v,sp) ->
   *   S.union (free_vars_val k v) (sp_vars sp) *)
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

  let pp = pp_value
    
end

module ValuePdConv = PdConversion(ValuePdSyntax)

let string_pd_to_value_tele (c : string) (pd : string Pd.pd) : value tele = 
  ValuePdConv.string_pd_to_tele c pd 

(*****************************************************************************)
(*                              Value Cylinders                              *)
(*****************************************************************************)

module ValueCylinderSyntax = struct
  include ValuePdSyntax
  
  let ucomp c pd =
    if (Pd.is_disc pd) then
      head (Pd.labels pd)
    else
      let v = eval Emp Emp (UCompT (UnitPd (Pd.blank pd))) in 
      appArgs v (pd_args c pd)

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
