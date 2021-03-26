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

  | UCompT uc -> UCompV (uc,EmpSp)
  | CohT (g,c,s,t) -> CohV (eval top loc (tele_to_pi g (HomT (c,s,t))),EmpSp)
  | CylCohT (_,_,_,_) -> failwith "eval cylcoh"
                        
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
  | CohV (v,sp) -> CohV (v,AppSp(sp,u,ict))
  | LamV (_,_,cl) -> cl $$ u
  | _ -> raise (Eval_error "malformed application")

and baseV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,BaseSp sp)
  | RigidV (i,sp) -> RigidV (i,BaseSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,BaseSp sp, baseV tv)
  | CohV (ga,sp) -> CohV (ga,BaseSp sp)
  | CylV (b,_,_) -> b 
  | _ -> raise (Eval_error "malformed base projection")

and lidV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,LidSp sp)
  | RigidV (i,sp) -> RigidV (i,LidSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,LidSp sp, lidV tv)
  | CohV (ga,sp) -> CohV (ga,LidSp sp)
  | CylV (_,l,_) -> l
  | _ -> raise (Eval_error "malformed lid projection")

and coreV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,CoreSp sp)
  | RigidV (i,sp) -> RigidV (i,CoreSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,CoreSp sp, coreV tv)
  | CohV (ga,sp) -> CohV (ga,CoreSp sp)
  | CylV (_,_,c) -> c
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

let rec quote k v ufld =
  let qc x = quote k x ufld in
  let qcs x s = quote_sp k x s ufld in 
  match force_meta v with
  | FlexV (m,sp) -> qcs (MetaT m) sp 
  | RigidV (l,sp) -> qcs (VarT (lvl_to_idx k l)) sp 
  | TopV (_,_,tv) when ufld -> qc tv 
  | TopV (nm,sp,_) -> qcs (TopT nm) sp 
  | LamV (nm,ict,cl) -> LamT (nm, ict, quote (k+1) (cl $$ varV k) ufld)
  | PiV (nm,ict,u,cl) -> PiT (nm, ict, qc u, quote (k+1) (cl $$ varV k) ufld)
  | ObjV c -> ObjT (qc c)
  | HomV (c,s,t) -> HomT (qc c, qc s, qc t)

  | UCompV (uc,sp) when ufld ->
    qcs (term_ucomp_coh (ucmp_pd uc)) sp 
  | UCompV (uc,sp) -> qcs (UCompT uc) sp
  | CohV (v,sp) ->

    let pi_tm = quote k v ufld in
    let (g,a) = pi_to_tele pi_tm in
    (match a with
     | HomT (c,s,t) -> qcs (CohT (g,c,s,t)) sp
     | _ -> failwith "invalid coherence return type")
                        
  | CylCohV (_,_) -> failwith "quote cylcoh"

  | CylV (b,l,c) -> CylT (qc b, qc l, qc c)
  | ArrV c -> ArrT (qc c)
  | CatV -> CatT
  | TypV -> TypT

and quote_sp k t sp ufld =
  let qc x = quote k x ufld in
  let qcs x s = quote_sp k x s ufld in 
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
      let ty_tm = quote k typ true in
      (Ext (r,(nm,ict,ty_tm)),k+1)
  in fst (go tl)

let nf top loc tm =
  quote (length loc) (eval top loc tm) true

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
  | UCompV (_,sp) -> sp_vars sp 
  | CohV (v,sp) ->
    S.union (free_vars_val k v) (sp_vars sp)
  | CylCohV _ -> failwith "fvs cylcohv"
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

let value_fixup (pd : string Pd.pd) : (value decl) Pd.pd =
  (Pd.pd_lvl_map pd (fun s l -> (s,Impl, varV (l+1))))
  
let string_pd_to_value_tele (pd : string Pd.pd) : value tele = 
  ValuePdConv.pd_to_tele (varV 0) (value_fixup pd)

(*****************************************************************************)
(*                              Value Coherences                             *)
(*****************************************************************************)

(* could have an initial level .... *)
(* let rec quote_tele (ufld : bool) (tl : value tele) : term tele * lvl =
 *   match tl with
 *   | Emp -> (Emp,0)
 *   | Ext (tl',(nm,ict,v)) ->
 *     let (tl'',lvl) = quote_tele ufld tl' in
 *     let t = quote lvl v ufld in
 *     (Ext (tl'',(nm,ict,t)),lvl+1)
 * 
 * (\* val coh : s tele -> s -> s -> s -> s *\)
 * let val_coh (g : value tele) (c : value) (s : value) (t : value) : value =
 * 
 *   (\* Is it actually necessary to unfold here? *\)
 *   let (gt,lvl) = quote_tele true g in
 *   let ct = quote lvl c true in
 *   let st = quote lvl s true in
 *   let tt = quote lvl t true in
 * 
 *   let cohtm = CohT (gt,ct,st,tt) in
 *   eval Emp Emp cohtm  *)
