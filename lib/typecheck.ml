(*****************************************************************************)
(*                                                                           *)
(*                                Typechecking                               *)
(*                                                                           *)
(*****************************************************************************)

open Pd
open Suite
open Term
open Expr 

open Cheshire.Err
open Cheshire.Monad

open Format

(*****************************************************************************)
(*                             Typechecking Monad                            *)
(*****************************************************************************)

type normalization_type =
  | None
  | StrictlyUnital

(* Global option, or part of type checking config? *)
let norm_opt = ref None
    
type tc_def =
  | TCCohDef of tm_term pd * ty_term 
  | TCTermDef of ty_term suite * ty_term * tm_term

type tc_env = {
    gma : ty_term suite;
    rho : (string * tc_def) suite;
    tau : (string * int) suite;
  }

let empty_env = { gma = Emp ; rho = Emp ; tau = Emp }

type 'a tcm = tc_env -> 'a err

module TcMonad = MakeMonadError(struct

    type 'a t = 'a tcm
        
    let map f m env =
      match m env with
      | Ok a -> Ok (f a)
      | Fail s -> Fail s

    let pure a _ = Ok a
        
    let bind m f env =
      match m env with
      | Fail s -> Fail s
      | Ok a -> f a env

  end)(struct

    type e = string

    let throw s _ = Fail s
    let catch m h env =
      match m env with
      | Ok a -> Ok a
      | Fail s -> h s env
        
  end)

open TcMonad
open TcMonad.MonadSyntax

let tc_ok = pure
let tc_fail = throw

let tc_in_ctx g m env = m { env with gma = g }
let tc_ctx env = Ok env.gma
let tc_env env = Ok env
let tc_with_env e m _ = m e
let tc_lift m _ = m
let tc_depth env = Ok (length env.gma)
    
let tc_with_coh id pd typ m env =
  m { env with rho = Ext (env.rho, (id, TCCohDef (pd,typ))) }
let tc_with_let id gma ty tm m env =
  m { env with rho = Ext (env.rho, (id, TCTermDef (gma,ty,tm))) }
                      
let tc_lookup_var i env =
  err_lookup_var i env.gma

let tc_lookup_def id env =
  try Ok (assoc id env.rho)
  with Not_found -> Fail (sprintf "Unknown cell identifier: %s" id)

let tc_id_to_level id env =
  try Ok (assoc id env.tau)
  with Not_found -> Fail (sprintf "Unknown variable identifier: %s" id)

module ST = SuiteTraverse(TcMonad)

let rec tc_unfold_ty ty =
  match ty with
  | ObjT -> tc_ok ObjT
  | ArrT (typ,src,tgt) ->
    let* typ' = tc_unfold_ty typ in
    let* src' = tc_unfold_tm src in
    let* tgt' = tc_unfold_tm tgt in
    tc_ok (ArrT (typ',src',tgt'))
    
and tc_unfold_tm tm =
  match tm with
  | VarT i -> tc_ok (VarT i)
  | DefAppT (id, sub) -> (
    let* sub' = ST.traverse tc_unfold_tm sub in 
    let* def = tc_lookup_def id in
    match def with
    | TCCohDef (pd,typ) ->
      let* typ' = tc_unfold_ty typ in 
      tc_ok (CohT (pd,typ',sub'))
    | TCTermDef (_, _, tm) -> 
      tc_ok (subst_tm sub' tm)
  )
  | CohT (pd,typ,sub) ->
    let* sub' = ST.traverse tc_unfold_tm sub in
    let* typ' = tc_unfold_ty typ in 
    tc_ok (CohT (pd,typ',sub'))

(*****************************************************************************)
(*                         Strict Unit Normalization                         *)
(*****************************************************************************)

let rec id_typ k =
  if (k <= 0) then ObjT else
    ArrT (id_typ (k-1), VarT (2*k - 2), VarT (2*k - 1))

let id_cell k =
  (pd_to_db (disc k),
   ArrT (id_typ k, VarT (2*k), VarT (2*k)))
  
let identity_on ty tm =
  let (id_pd, id_ty) = id_cell (dim_typ ty) in
  CohT (id_pd, id_ty, disc_sub ty tm)

(* Extract the type of the current
   focus in a pasting diagram context *)
let rec ctx_typ ctx =
  match ctx with
  | Emp -> ObjT
  | Ext (ctx',(s,t,_,_)) ->
    ArrT (ctx_typ ctx', s, t)

(* Not used currently ... *)
let match_identity tm =
  match tm with
  | CohT (pd,typ,args) ->
    let (id_pd, id_ty) = id_cell (dim_pd pd) in
    if (pd = id_pd && typ = id_ty) then
      Ok (last args)
    else
      Fail "Not an identity"
  (* perhaps you should unfold? *)
  | _ -> Fail "Not an identity"

let is_identity tm =
  (* printf "Checking if term is ident: %a@," pp_print_tm tm; *)
  match tm with
  | CohT (pd,typ,_) ->
    (* let (id_pd,id_typ) = id_cell (dim_pd pd) in
     * printf "Expected id cell: @[<hov>%a:%a@]@," pp_print_term_pd id_pd pp_print_ty id_typ; *)
    (pd,typ)=(id_cell (dim_pd pd))
  | _ -> false

let (>>==) = ErrMonad.(>>=)
let (<||>) = ErrMonad.(<||>)

type prune_result =
  | NothingPruned
  | PrunedData of (tm_term pd * tm_term suite * tm_term suite)

(* Assumes we are at a leaf.  Finds the next
   (moving right) leaf with a prunable term
   or fails *)
let rec next_prunable z =
  (* printf "At leaf: %a@," pp_print_term_pd (snd z); *)
  if (is_identity (label_of (snd z))) then Ok z
  else leaf_right z >>==
    next_prunable

let prune_once pd =
  let open ErrMonad.MonadSyntax in 
  let* lz = to_leftmost_leaf (Emp,pd) in
  match next_prunable lz with
  | Fail _ -> Ok NothingPruned
  | Ok pz ->

    (* printf "Found a prunable argument: %a@," pp_print_tm (label_of (snd pz)); *)
    
    let* (addr,dir) = (
      match addr_of pz with
      | Emp -> Fail "Invalid address during pruning"
      | Ext(a,d) -> Ok (a,d)
    ) in

    (* printf "Address: %a@," pp_print_addr (Ext(addr,dir)); *)
    
    let* dz = pd_drop pz in
    let pd' = pd_close dz in
    let db_pd = pd_to_db pd' in

    (* printf "New pasting diagram is: %a@," pp_print_term_pd db_pd; *)

    let* (ctx,fcs) = seek addr (Emp, db_pd) in

    (* printf "Seek has focus: %a@," pp_print_term_pd fcs; *)
    
    let* newfcs = 
      (match fcs with
       | Br (s,brs) ->
         let id_ty = ctx_typ ctx in
         let id_tm = identity_on id_ty s in 
         let id_br = Br (id_tm, Emp) in
         let (l,r) = split_at dir brs in
         let src = (match l with
           | Emp -> s
           | Ext(_,(t,_)) -> t) in 
         Ok (Br (s, append_list (Ext (l,(src,id_br))) r))) in

    (* printf "Got new focus@,"; *)
    
    let pi_pd = pd_close (ctx, newfcs) in 

    let pi = labels pi_pd in 
    let sigma = labels pd' in

    (* printf "pi: %a@," pp_print_sub pi;
     * printf "sigma: %a@," pp_print_sub sigma; *)
    
    Ok (PrunedData (db_pd, pi, sigma))

let rec prune pd typ args =
  let open ErrMonad.MonadSyntax in 
  let* arg_pd = args_to_pd pd args in 
  let* pr = prune_once arg_pd in
  match pr with
  | NothingPruned -> Ok (pd,typ,args)
  | PrunedData (pd',pi,args') ->
    (* printf "Pruned an argument!@,"; *)
    prune pd' (subst_ty pi typ) args'

let disc_cell k =
  (pd_to_db (disc k), id_typ k)

let disc_remove pd typ sub =
  (* match tm with
   * | VarT i -> Ok (VarT i)
   * | CohT (pd, typ, sub) -> *)
    if ((pd,typ) = disc_cell (dim_pd pd)) then
      Ok (last sub)
    else Ok (CohT (pd,typ,sub))
  (* | _ -> Fail "unfold in disc remove" *)

type endo_result =
  | NoEndoReduction
  | EndoReduced of tm_term

let endo_coherence tm =
  let nored = Ok NoEndoReduction in
  (* printf "In endo coh with: %a@," pp_print_tm tm;  *)
  match tm with
  | VarT _ -> nored
  | CohT (_, ObjT, _) -> nored
  | CohT (_, ArrT (btyp,src,tgt), sub) -> 
    if (src = tgt) then
      let src' = subst_tm sub src in
      let typ' = subst_ty sub btyp in 
      (* printf "Endo-coherence for: %a@," pp_print_tm src; *)
      Ok (EndoReduced (identity_on typ' src'))
    else nored
  | _ -> Fail "Unfold in endo-coh"

let rec strict_unit_normalize_ty ty =
  match ty with
  | ObjT -> tc_ok ObjT
  | ArrT (typ,src,tgt) ->
    let* typ' = strict_unit_normalize_ty typ in
    let* src' = strict_unit_normalize_tm src in
    let* tgt' = strict_unit_normalize_tm tgt in 
    tc_ok (ArrT (typ',src',tgt'))

and strict_unit_normalize_tm ?debug:(dbg=false) tm =
  (* let print_debug s = if dbg then printf "%s" s else () in *)
  (* print_debug (asprintf "In su normalizer ...@,"); *)
  if dbg then () else ();
  match tm with
  | VarT i -> tc_ok (VarT i)
  | DefAppT (id, sub) -> (
    let* def = tc_lookup_def id in
    match def with
    | TCCohDef (pd,typ) ->
      (* print_debug (asprintf "Normalizing a defined coherence@,"); *)
      strict_unit_normalize_tm ~debug:true (CohT (pd,typ,sub))
    | TCTermDef (_, _, tm) -> 
      strict_unit_normalize_tm (subst_tm sub tm)
  )
  | CohT (pd,typ,sub) ->
    (* print_debug (asprintf "Normalizing a coherence@,"); *)
    let* sub' = ST.traverse strict_unit_normalize_tm sub in
    let* (ppd,ptyp,psub) = 
      if (not (is_identity tm)) then
        tc_lift (prune pd typ sub')
      else tc_ok (pd,typ,sub') in
    (* printf "After pruning: %a@," pp_print_tm (CohT (ppd,ptyp,psub)); *)
    let* typ' = strict_unit_normalize_ty ptyp in
    (* print_debug (asprintf "Normalized boundary: %a@," pp_print_ty typ'); *)
    let* dtm = tc_lift (disc_remove ppd typ' psub) in
    if (not (is_identity dtm)) then
      let* er = tc_lift (endo_coherence dtm) in
      match er with
      | NoEndoReduction -> tc_ok dtm
      | EndoReduced tm' ->
        (* print_debug (asprintf "Reduced an endo-coherence@,"); *)
        (* printf "Endo coherence resulted in: %a@," pp_print_tm tm'; *)
        strict_unit_normalize_tm tm'
    else tc_ok dtm 

(*****************************************************************************)
(*                           Toplevel Normalization                          *)
(*****************************************************************************)

let tc_normalize_tm ?debug:(dbg=false) tm =
  match !norm_opt with
  | None -> tc_ok tm
  | StrictlyUnital -> strict_unit_normalize_tm ~debug:dbg tm 

let tc_normalize_ty ty =
  match !norm_opt with
  | None -> tc_ok ty
  | StrictlyUnital -> strict_unit_normalize_ty ty
    
let tc_eq_nf_ty tya tyb =
  let* tya_nf = tc_normalize_ty tya in
  let* tyb_nf = tc_normalize_ty tyb in
  if (tya_nf = tyb_nf)
  then tc_ok ()
  else tc_fail "Type mismatch"

(*****************************************************************************)
(*                                Typing Rules                               *)
(*****************************************************************************)

let rec tc_check_ty t = 
  match t with
  | ObjT -> tc_ok ObjT
  | ArrT (typ, src, tgt) ->
    let* typ' = tc_check_ty typ in
    let* src' = tc_check_tm src typ' in
    let* tgt' = tc_check_tm tgt typ' in
    tc_ok (ArrT (typ', src', tgt'))

and tc_check_tm tm ty =
  let* (tm', ty') = tc_infer_tm tm in

  (* let* ty_nf = tc_normalize_ty ty in
   * let* ty_nf' = tc_normalize_ty ty' in 
   * if (ty_nf = ty_nf') then
   *   tc_ok tm'
   * else let msg = asprintf "%a =/= %a (in nf) when inferring the type of %a"
   *          pp_print_ty ty_nf
   *          pp_print_ty ty_nf'
   *          pp_print_tm tm
   *       in tc_fail msg *)
  
  let* _ = catch (tc_eq_nf_ty ty ty')
  
      (fun _ -> let msg = asprintf "%a =/= %a when inferring the type of %a"
                    pp_print_ty ty
                    pp_print_ty ty'
                    pp_print_tm tm
        in tc_fail msg) in 
  
  tc_ok tm'

and tc_infer_tm tm =
  match tm with
  
  | VarT i ->
    let* typ = tc_lookup_var i in
    tc_ok (VarT i , typ)
      
  | DefAppT (id, sub) -> (
    let* def = tc_lookup_def id in
    match def with
    | TCCohDef (pd,typ) -> 
      let pd_ctx = pd_to_ctx pd in
      let* sub' = tc_check_args sub pd_ctx in
      tc_ok (DefAppT (id, sub'), subst_ty sub' typ)
    | TCTermDef (ctx, typ, _) -> 
      let* sub' = tc_check_args sub ctx in
      tc_ok (DefAppT (id, sub'), subst_ty sub' typ)
  )
                      
  | CohT (pd, typ, sub) ->
    let pd_ctx = pd_to_ctx pd in
    let* typ' = tc_in_ctx pd_ctx
        (let* rtyp = tc_check_ty typ in
         tc_check_is_full pd rtyp) in 
    (* Check the substitution and calculate the return type *)
    let* sub' = tc_check_args sub pd_ctx in
    tc_ok (CohT (pd, typ', sub'), subst_ty sub' typ')

and tc_check_is_full pd typ =
  let pd_dim = dim_pd pd in
  printf "Checking fullness...";
  (* printf "Pd: %a@," (pp_print_pd pp_print_tm) pd;
   * printf "Type: @[<hov>%a@]@," pp_print_ty typ; *)
  match typ with
  | ObjT -> tc_fail "No coherences have object type."
  | ArrT (btyp,src,tgt) -> 
    let* src_pd = tc_term_pd src in
    let* tgt_pd = tc_term_pd tgt in
    let typ_dim = dim_typ btyp in
    if (typ_dim >= pd_dim) then
      let _ = () in printf "Checking coherence@,";
      let* _ = ensure (src_pd = pd) ("Non-full source in coherence") in
      let* _ = ensure (tgt_pd = pd) ("Non-full target in coherence") in
      tc_ok typ
    else
      let _ = () in printf "Checking composite@,";
      let pd_src = truncate true (pd_dim - 1) pd in
      let pd_tgt = truncate false (pd_dim - 1) pd in
      (* printf "Expected source pd: %a@," (pp_print_pd pp_print_tm) pd_src;
       * printf "Provided source pd: %a@," (pp_print_pd pp_print_tm) src_pd;
       * printf "Expected target pd: %a@," (pp_print_pd pp_print_tm) pd_tgt;
       * printf "Provided target pd: %a@," (pp_print_pd pp_print_tm) tgt_pd; *)
      let* _ = ensure (src_pd = pd_src) ("Non-full source in composite") in
      let* _ = ensure (tgt_pd = pd_tgt) ("Non-full target in composite") in 
      tc_ok typ
    
and tc_check_args sub gma =
  match (sub,gma) with
  | (Ext (_,_), Emp) -> tc_fail "Too many arguments!"
  | (Emp, Ext (_,_)) -> tc_fail "Not enough arguments!"
  | (Emp, Emp) -> tc_ok Emp
  | (Ext (sub',tm), Ext (gma',typ)) ->
    let* rsub = tc_check_args sub' gma' in
    let typ' = subst_ty rsub typ in
    let* rtm = tc_check_tm tm typ' in
    tc_ok (Ext (rsub, rtm))
    
(* Extract the pasting diagram of a well typed term.
 * Note that the term is assumed to be well typed in 
 * the current context *)
      
and tc_term_pd tm =
  match tm with
  | VarT i -> 
    let* typ = tc_lookup_var i in
    tc_ok (disc_pd typ (VarT i))
  | DefAppT (id , args) -> (
    let* def = tc_lookup_def id in
    match def with
    | TCCohDef (pd,typ) ->
      tc_term_pd (CohT (pd,typ,args))
    | TCTermDef (_, _, tm) ->
      tc_term_pd (subst_tm args tm)
  )    
  | CohT (pd, _, sub) -> 
    let* pd_sub = ST.traverse tc_term_pd sub in
    let* ppd = tc_lift (args_to_pd pd pd_sub) in
    (* printf "To Join: %a@," (pp_print_pd (pp_print_pd pp_print_tm)) ppd; *)
    let jres = join_pd 0 ppd in
    (* printf "Result: %a@," (pp_print_pd pp_print_tm) jres; *)
    tc_ok jres 
    
(*****************************************************************************)
(*                        Typechecking Raw Expressions                       *)
(*****************************************************************************)

module SM = SuiteMonad
  
let rec expr_tc_check_ty typ = 
    
  match typ with
  | ObjE -> tc_ok ObjT
  | ArrE (src, tgt) -> 
    let* (src_tm, src_ty) = expr_tc_infer_tm src in
    let* (tgt_tm, tgt_ty) = expr_tc_infer_tm tgt in

    let* _ = catch (tc_eq_nf_ty src_ty tgt_ty) 

      (fun _ -> let msg = asprintf "%a =/= %a when checking that %a is a valid type"
                    pp_print_ty src_ty
                    pp_print_ty tgt_ty
                    pp_print_expr_ty typ
        in tc_fail msg) in 
    
    tc_ok (ArrT (src_ty, src_tm, tgt_tm))

and expr_tc_check_tm tm ty =
  
  let* (tm', ty') = expr_tc_infer_tm tm in
  
  let* ty_nf = tc_normalize_ty ty in
  let* ty_nf' = tc_normalize_ty ty' in 
  if (ty_nf = ty_nf') then
    tc_ok tm'
  else let msg = asprintf "%a =/= %a (in nf) when inferring the type of %a"
           pp_print_ty ty_nf
           pp_print_ty ty_nf'
           pp_print_expr_tm tm
        in tc_fail msg
  
  (* let* _ = catch (tc_eq_nf_ty ty ty')
   * 
   *     (fun _ -> let msg = asprintf "%a =/= %a when inferring the type of %a"
   *                   pp_print_ty ty
   *                   pp_print_ty ty'
   *                   pp_print_expr_tm tm
   *       in tc_fail msg) in 
   * 
   * tc_ok tm' *)
  
and expr_tc_infer_tm tm = 

  match tm with
  
  | VarE id ->
    let* l = tc_id_to_level id in
    let* typ = tc_lookup_var l in

    (* printf "Looking up id: %s@," id;
     * printf "Result type: %a@," pp_print_ty typ; *)
    
    tc_ok (VarT l, typ)

  | DefAppE (id, args) -> (
    let* def = tc_lookup_def id in
    match def with
    | TCCohDef (pd,typ) ->

      (* printf "Extracted defined coherence: %s@," id; *)

      let args_map = zip (leaves pd) args in
      let* (_, arg_pd) = expr_pd_infer_args pd args_map in 
      let args' = labels arg_pd in

      (* printf "Inferred arguments:@,%a@," (pp_print_suite pp_print_tm) args'; *)

      let* args'' = tc_check_args args' (pd_to_ctx pd) in 
      
      tc_ok (DefAppT (id, args''), subst_ty args'' typ)
    
    | TCTermDef (gma, typ, _) -> 
      let* args' = expr_tc_check_args args gma in
      tc_ok (DefAppT (id, args'), subst_ty args' typ)
  )

  | CohE (tele, typ, args) ->
    let* (gma, pd, typ') = expr_tc_check_coh tele typ in
    let* args' = expr_tc_check_args args gma in
    tc_ok (CohT (pd,typ',args'), subst_ty args' typ')
    
and expr_tc_check_args sub gma =
  match (sub,gma) with
  | (Ext (_,_), Emp) -> tc_fail "Too many arguments!"
  | (Emp, Ext (_,_)) -> tc_fail "Not enough arguments!"
  | (Emp, Emp) -> tc_ok Emp
  | (Ext (sub',tm), Ext (gma',typ)) ->
    let* rsub = expr_tc_check_args sub' gma' in
    let typ' = subst_ty rsub typ in
    let* rtm = expr_tc_check_tm tm typ' in
    tc_ok (Ext (rsub, rtm))

(* run the computation m in the context given 
 * by the telescope, checking as one goes that
 * the telescope is valid *)

(* because this is only used once in this file, it is not given a
   general enough type.  But it is used later in the command module.
   Anyway to fix this? *)
      
and expr_tc_in_tele : 'a. tele -> 'a tcm -> 'a tcm = 
  fun tele m -> 
  match tele with
  | Emp ->
    let* env = tc_env in
    tc_with_env { gma = Emp ; rho = env.rho ; tau = Emp } m 
  | Ext (tele',(id,typ)) -> 
    expr_tc_in_tele tele'
      (let* typ' = expr_tc_check_ty typ in
       let* env = tc_env in
       let* d = tc_depth in 
       let env' = {
         gma = Ext (env.gma, typ');
         rho = env.rho;
         tau = Ext (env.tau, (id,d))
       } in 
       tc_with_env env' m)

and expr_tc_check_coh tele typ = 
  expr_tc_in_tele tele
    (let* typ' = expr_tc_check_ty typ in
     let* gma = tc_ctx in
     (* printf "Telescope: %a@," pp_print_ctx gma; *)
     let* pd = tc_lift (ctx_to_pd gma) in
     let* _ = tc_check_is_full pd typ' in
     tc_ok (gma, pd, typ'))

and expr_pd_infer_args pd args_map =
  match pd with
  | Br (l,Emp) ->
    let arg = assoc l args_map in
    let* (arg_tm, arg_typ) = expr_tc_infer_tm arg in 
    tc_ok (arg_typ, Br (arg_tm,Emp))
  | Br (_,brs) ->
    let lcl (_,b) = 
      let* (arg_typ, arg_br) = expr_pd_infer_args b args_map in
      (match arg_typ with
       | ObjT -> tc_fail "something"
       | ArrT (typ,src,tgt) ->
         tc_ok (typ,src,(tgt,arg_br))) in 
    let* branch_results = ST.traverse lcl brs in
    let (t,s,_) = first branch_results in
    let branches = SM.map (fun (_,_,b) -> b) branch_results in
    tc_ok (t, Br(s,branches))
    
