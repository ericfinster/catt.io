(*****************************************************************************)
(*                                                                           *)
(*                                Typechecking                               *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Pd
open Suite
open Term
open Expr
    
open Mtl

(*****************************************************************************)
(*                             Typechecking Monad                            *)
(*****************************************************************************)

type normalization_type =
  | None
  | StrictlyUnital

type tc_config = {
  norm_type: normalization_type;
  debug_streams: (string * int) list;
}

let default_config = {
  norm_type = None;
  debug_streams = [];
}

type tc_err =
  | TypeMismatch of (tm_term * ty_term * ty_term)
  | InvalidIndex of int 
  | UnknownIdentifier of string
  | NonFullSource of (tm_term pd * tm_term pd)
  | NonFullTarget of (tm_term pd * tm_term pd)
  | UnderApplication
  | OverApplication
  | InternalError of string 

let print_tc_err terr =
  match terr with
  | TypeMismatch (tm,ex_ty,in_ty) ->
    asprintf "@[<v>The term@,@,%a@,@,was expected to have type@,@,%a@,@,but was inferred to have type@,@,%a@]"
      pp_print_expr_tm (term_to_expr_tm_default tm)
      pp_print_expr_ty (term_to_expr_ty_default ex_ty)
      pp_print_expr_ty (term_to_expr_ty_default in_ty)
  | InvalidIndex i -> sprintf "Unknown variable index %d" i 
  | UnknownIdentifier s -> sprintf "Unknown identifier %s" s
  | NonFullSource (_, _) -> "Non-full source"
  | NonFullTarget (_, _) -> "Non-full target"
  | UnderApplication -> "Not enough arguments"
  | OverApplication -> "Too many arguments"
  | InternalError s -> s

type tc_def =
  | TCCohDef of tm_term pd * ty_term 
  | TCTermDef of ty_term suite * ty_term * tm_term

type tc_env = {
  gma : ty_term suite;
  rho : (string * tc_def) suite;
  config : tc_config;
  modules : string list;
}

let empty_env = {
  gma = Emp ;
  rho = Emp ;
  config = default_config;
  modules = [];
}

(* module StringErr = ErrMnd(struct type t = string end) *)
module TcErrMnd = ErrMnd(struct type t = tc_err end)
module TcmMnd = ReaderT(struct type t = tc_env end)(TcErrMnd)

(* Bring syntax into scope *)
open TcmMnd
open MonadSyntax(TcmMnd)

type 'a tcm = 'a TcmMnd.m
    
let tc_ok a = pure a
let tc_fail e = lift (Fail e)

(* Not sure how to lift the lower error instance effectively ... *)
let tc_catch m f env = 
  match m env with
    | Ok a -> Ok a
    | Fail s -> f s env

let ensure b e =
  if b then tc_ok ()
  else tc_fail e
      
let tc_in_ctx g m env = m { env with gma = g }
let tc_ctx env = Ok env.gma
let tc_env env = Ok env
let tc_with_env e m _ = m e
let tc_lift m _ = m
let tc_depth env = Ok (length env.gma)
let tc_from_str_err m _ =
  match m with
  | Ok a -> Ok a
  | Fail s -> Fail (InternalError s)

let tc_with_coh id pd typ m env =
  m { env with rho = Ext (env.rho, (id, TCCohDef (pd,typ))) }
let tc_with_let id gma ty tm m env =
  m { env with rho = Ext (env.rho, (id, TCTermDef (gma,ty,tm))) }
                      
let tc_lookup_var i env =
  try Ok (nth i env.gma)
  with Not_found -> Fail (InvalidIndex i)

let tc_lookup_def id env =
  try Ok (assoc id env.rho)
  with Not_found -> Fail (UnknownIdentifier id)

(*****************************************************************************)
(*                             Debugging routines                            *)
(*****************************************************************************)

let tc_dump_rho =
  let* env = tc_env in
  fprintf std_formatter "Environment: %a@,"
    (pp_print_suite_horiz (fun ppf (id,_) -> fprintf ppf "%s" id)) env.rho; 
  tc_ok ()

(*****************************************************************************)
(*                                 Unfolding                                 *)
(*****************************************************************************)
                      
module ST = SuiteTraverse(MndToApp(TcmMnd))

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
      let* tm' = tc_unfold_tm tm in 
      tc_ok (subst_tm sub' tm')
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

let (>>==) = StringErr.bind
let (<||>) = StringErr.(<||>)

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
  let open MonadSyntax(StringErr) in 
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
  let open MonadSyntax(StringErr) in 
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
        tc_from_str_err (prune pd typ sub')
      else tc_ok (pd,typ,sub') in
    (* printf "After pruning: %a@," pp_print_tm (CohT (ppd,ptyp,psub)); *)
    let* typ' = strict_unit_normalize_ty ptyp in
    (* print_debug (asprintf "Normalized boundary: %a@," pp_print_ty typ'); *)
    let* dtm = tc_lift (disc_remove ppd typ' psub) in
    if (not (is_identity dtm)) then
      let* er = tc_from_str_err (endo_coherence dtm) in
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
  let* env = tc_env in
  match env.config.norm_type with 
  | None -> tc_unfold_tm tm
  | StrictlyUnital -> strict_unit_normalize_tm ~debug:dbg tm 

let tc_normalize_ty ty =
  let* env = tc_env in
  match env.config.norm_type with 
  | None -> tc_unfold_ty ty
  | StrictlyUnital -> strict_unit_normalize_ty ty
    
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
  let* ty_nf = tc_normalize_ty ty in
  let* ty_nf' = tc_normalize_ty ty' in 
  if (ty_nf = ty_nf') then
    tc_ok tm'
  else
    tc_fail (TypeMismatch (tm,ty,ty'))
  
  (* let* _ = tc_catch (tc_eq_nf_ty ty ty')
   * 
   *     (fun _ -> let msg = asprintf "@[<v>The term@,@,%a@,@,was expected to have type@,@,%a@,@,but was inferred to have type@,@,%a@]"
   *                   pp_print_expr_tm (term_to_expr_tm tm)
   *                   pp_print_expr_ty (term_to_expr_ty ty)
   *                   pp_print_expr_ty (term_to_expr_ty ty')
   *       in tc_fail msg) in 
   * 
   * tc_ok tm' *)

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
  (* printf "Checking fullness..."; *)
  (* printf "Pd: %a@," (pp_print_pd pp_print_tm) pd;
   * printf "Type: @[<hov>%a@]@," pp_print_ty typ; *)
  match typ with
  | ObjT -> tc_fail (InternalError "Coherence cannot have object type")
  | ArrT (btyp,src,tgt) -> 
    let* src_pd = tc_term_pd src in
    let* tgt_pd = tc_term_pd tgt in
    let typ_dim = dim_typ btyp in
    if (typ_dim >= pd_dim) then
      (* let _ = () in printf "Checking coherence@,"; *)
      let* _ = ensure (src_pd = pd) (NonFullSource (src_pd, pd)) in
      let* _ = ensure (tgt_pd = pd) (NonFullTarget (tgt_pd, pd)) in
      tc_ok typ
    else
      (* let _ = () in printf "Checking composite@,"; *)
      let pd_src = truncate true (pd_dim - 1) pd in
      let pd_tgt = truncate false (pd_dim - 1) pd in
      (* printf "Expected source pd: %a@," (pp_print_pd pp_print_tm) pd_src;
       * printf "Provided source pd: %a@," (pp_print_pd pp_print_tm) src_pd;
       * printf "Expected target pd: %a@," (pp_print_pd pp_print_tm) pd_tgt;
       * printf "Provided target pd: %a@," (pp_print_pd pp_print_tm) tgt_pd; *)
      let* _ = ensure (src_pd = pd_src) (NonFullSource (src_pd, pd)) in
      let* _ = ensure (tgt_pd = pd_tgt) (NonFullTarget (tgt_pd, pd)) in 
      tc_ok typ
    
and tc_check_args sub gma =
  match (sub,gma) with
  | (Ext (_,_), Emp) -> tc_fail UnderApplication
  | (Emp, Ext (_,_)) -> tc_fail OverApplication 
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
    let* ppd = tc_from_str_err (args_to_pd pd pd_sub) in
    (* printf "To Join: %a@," (pp_print_pd (pp_print_pd pp_print_tm)) ppd; *)
    let jres = join_pd 0 ppd in
    (* printf "Result: %a@," (pp_print_pd pp_print_tm) jres; *)
    tc_ok jres 



