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
open Scheme

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

exception Eval_error of string

module Make (R : ReductionScheme) = struct

  let rec eval top loc tm =
    (* log_val "Evaluating" tm (pp_term_gen ~si:true); *)
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
    | FlexV (m,sp) -> FlexV (m,AppSp(sp,u,ict))
    | RigidV (i,sp) -> RigidV (i,AppSp(sp,u,ict))
    | TopV (nm,sp,tv) ->
       TopV (nm,AppSp(sp,u,ict), appV tv u ict)
    | LamV (_,_,cl) -> cl $$ u
    | UCompV (ucd,cohv,sp) ->
       UCompV (ucd, appV cohv u ict ,AppSp(sp,u,ict))
    | CohV (cn,pd,c,s,t,sp) ->
       let sp' = AppSp(sp,u,ict) in
       (* log_val "To reduce" (CohV (cn,pd,c,s,t,sp)) pp_value; *)
       cohReduction cn pd c s t sp' (CohV (cn,pd,c,s,t,sp'))
    | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

  and alt_list (xs : (unit -> ('a , 'b) result) list) =
    match xs with
    | [] -> Error "Empty alt list"
    | x :: [] -> x ()
    | x :: xs -> match x () with
                 | Ok x -> Ok x
                 | Error x -> (match alt_list xs with
                               | Ok y -> Ok y
                               | Error y -> Error (Printf.sprintf "%s | %s" x y))

  and cohReduction cn pd c s t sp' fallback =
    match (cohReduction' cn pd c s t sp') with
    | Ok v -> v
    | Error x -> fallback

  and unfold v =
      match force_meta v with
      | TopV (_,_,x) -> unfold x
      | UCompV (_,cohv,_) -> unfold cohv
      | y -> y

  and cohReduction' cn pd c s t sp' =
    let* sp_list = sp_to_suite sp' in
    let k = length sp_list in
    if k = pd_length pd + 1
    then
      let* v = alt_list (R.reductions cn pd k c s t sp_list) in
      (* log_val "Reduced" (CohV (cn,pd,c,s,t,sp')) pp_value; *)
      (* log_val "To" (unfold v) pp_value; *)
      match unfold v with
      | CohV(cn',pd',c',s',t', fsp) -> Ok (cohReduction cn' pd' c' s' t' fsp v)
      | _ -> Ok v
    else Error "Not applied enough arguments yet"

  and appLocV loc v =
    match loc with
    | Emp -> v
    | Ext (loc',u) -> appV (appLocV loc' v) u Expl

  and runSpV v sp =
    match sp with
    | EmpSp -> v
    | AppSp (sp',u,ict) -> appV (runSpV v sp') u ict

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

  and nf top loc tm =
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



(*****************************************************************************)
(*                              Value Cylinders                              *)
(*****************************************************************************)

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

end
