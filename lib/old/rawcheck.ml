(*****************************************************************************)
(*                                                                           *)
(*                          Raw Expression Checking                          *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Suite
open Pd
open Term
open Expr 
open Typecheck
    
open Mtl

(*****************************************************************************)
(*                                 Raw Monad                                 *)
(*****************************************************************************)
            
type raw_env = {
  tau : (string * int) suite;
  section_ids : string list;
  section_args : tm_expr suite; 
}

let empty_raw_env = { 
  tau = Emp ;
  section_ids = [] ;
  section_args = Emp
}

module RawErrMnd = ErrT(struct type t = string end)(TcmMnd)
module RawMnd = ReaderT(struct type t = raw_env end)(RawErrMnd)

(*
 * The ultimate type of the monad is therefore:
 * 'a m = raw_env -> tc_env -> (('a, string) err, tc_err) err  
 *)

open RawMnd
open MonadSyntax(RawMnd)
    
let raw_ok a = pure a
let raw_fail s = RawMnd.lift (RawErrMnd.throw s)
  
let raw_env = RawMnd.ask 
let raw_complete_env renv tenv = Ok (Ok (renv, tenv))
let raw_with_env renv tenv m _ _ =
  m renv tenv

let raw_id_to_level id =
  let* renv = raw_env in
  try raw_ok (assoc id renv.tau)
  with Not_found -> raw_fail (sprintf "Unknown variable identifier: %s" id)

(* Again, this is messy.  Is there something better? *)
let raw_with_coh id pd typ m =
  let* (renv, tenv) = raw_complete_env in
  let tenv' = { tenv with rho = Ext (tenv.rho, (id, TCCohDef (pd,typ))) } in 
  raw_with_env renv tenv' m 

let raw_with_let id gma ty tm m = 
  let* (renv, tenv) = raw_complete_env in
  let tenv' = { tenv with rho = Ext (tenv.rho, (id, TCTermDef (gma,ty,tm))) } in
  raw_with_env renv tenv' m 

let raw_is_section_decl id =
  let* renv = raw_env in
  raw_ok (List.mem id renv.section_ids)

(* Just catch the raw errors ... *)
let raw_catch m f renv tenv =
  match m renv tenv with
  | Ok (Ok a) -> Ok (Ok a)
  | Ok (Fail s) -> f s renv tenv
  | Fail terr -> Fail terr

(* Run a typechecking computation, catching errors and using
 * raw typechecking information to be more explicit.
 *)
let raw_run_tc m renv tenv =
  match m tenv with
  | Ok a -> Ok (Ok a)
  | Fail (TypeMismatch (tm,ety,ity)) ->
    let rev_var_map = map (fun (x,y) -> (y,x)) renv.tau in
    (* printf "Var map: %a@," (pp_print_suite (fun ppf (i,s) -> fprintf ppf "%d -> %s" i s)) rev_var_map; *)
    let var_lookup i =
      try VarE (Suite.assoc i rev_var_map)
      with Not_found -> VarE (sprintf "_x%d" i)
    in let the_tm = term_to_expr_tm var_lookup tm in
    let expected_ty = term_to_expr_ty var_lookup ety in
    let inferred_ty = term_to_expr_ty var_lookup ity in
    let msg = asprintf "@[<v>The term@,@,%a@,@,was expected to have type@,@,%a@,@,but was inferred to have type@,@,%a@]"
      pp_print_expr_tm the_tm
      pp_print_expr_ty expected_ty
      pp_print_expr_ty inferred_ty
    in Ok (Fail msg)
  | Fail terr -> Ok (Fail (print_tc_err terr))

(*****************************************************************************)
(*                             Readback Utilities                            *)
(*****************************************************************************)
                   
let raw_rev_var_map =
  let* renv = raw_env in
  raw_ok (map (fun (x,y) -> (y,x)) renv.tau)

let raw_readback_ty ty =
  let* var_map = raw_rev_var_map in 
  let var_lookup i = try VarE (Suite.assoc i var_map)
    with Not_found -> VarE (sprintf "_x%d" i) in
  raw_ok (term_to_expr_ty var_lookup ty)

let raw_readback_tm tm =
  let* var_map = raw_rev_var_map in 
  let var_lookup i = try VarE (Suite.assoc i var_map)
    with Not_found -> VarE (sprintf "_x%d" i) in
  raw_ok (term_to_expr_tm var_lookup tm)


(*****************************************************************************)
(*                              Raw Typechecking                             *)
(*****************************************************************************)

let rec raw_check_ty typ =
  match typ with
  | ObjE -> raw_ok ObjT
  | ArrE (src, tgt) ->
    
    let* (src_tm, src_ty) = raw_infer_tm src in
    let* (tgt_tm, tgt_ty) = raw_infer_tm tgt in
    let* src_ty_nf = raw_run_tc (tc_normalize_ty src_ty) in 
    let* tgt_ty_nf = raw_run_tc (tc_normalize_ty tgt_ty) in

    if (src_ty_nf <> tgt_ty_nf) then
      let* rb_src_ty = raw_readback_ty src_ty in 
      let* rb_tgt_ty = raw_readback_ty tgt_ty in 
      let msg = asprintf "@[<v>%a@,  =/=@,%a@,@,when checking that %a is a valid type"
          pp_print_expr_ty rb_src_ty
          pp_print_expr_ty rb_tgt_ty
          pp_print_expr_ty typ
      in raw_fail msg
    else raw_ok (ArrT (src_ty, src_tm, tgt_tm))
      
and raw_check_tm tm ty =
  let* (tm', ty') = raw_infer_tm tm in
  let* ty_nf = raw_run_tc (tc_normalize_ty ty) in
  let* ty_nf' = raw_run_tc (tc_normalize_ty ty') in 
  if (ty_nf = ty_nf') then raw_ok tm'
  else 
    let* rb_expected_ty = raw_readback_ty ty in
    let* rb_inferred_ty = raw_readback_ty ty' in 
    let msg = asprintf "@[<v>The term@,@,%a@,@,was expected to have type@,@,%a@,@,but was inferred to have type@,@,%a@]"
           pp_print_expr_tm tm
           pp_print_expr_ty rb_expected_ty
           pp_print_expr_ty rb_inferred_ty
    in raw_fail msg

and raw_infer_tm tm = 

  match tm with
  
  | VarE id ->
    let* l = raw_id_to_level id in
    let* typ = raw_run_tc (tc_lookup_var l) in

    (* printf "Looking up id: %s@," id;
     * printf "Result type: %a@," pp_print_ty typ; *)
    
    raw_ok (VarT l, typ)

  | DefAppE (id, args) -> (
    let* def = raw_run_tc (tc_lookup_def id) in
    match def with
    | TCCohDef (pd,typ) ->

      (* printf "Extracted defined coherence: %s@," id; *)

      let args_map = zip (leaves pd) args in
      let* (_, arg_pd) = raw_pd_infer_args pd args_map in 
      let args' = labels arg_pd in

      (* printf "Inferred arguments:@,%a@," (pp_print_suite pp_print_tm) args'; *)

      let* args'' = raw_run_tc (tc_check_args args' (pd_to_ctx pd)) in 
      
      raw_ok (DefAppT (id, args''), subst_ty args'' typ)
    
    | TCTermDef (gma, typ, _) ->
      let* is_sec_decl = raw_is_section_decl id in
      let* args' =
        if (is_sec_decl) then
          let* renv = raw_env in 
          raw_ok (append renv.section_args args)
        else raw_ok args in 
      let* args'' = raw_check_args args' gma in
      raw_ok (DefAppT (id, args''), subst_ty args'' typ)
  )

  | CohE (tele, typ, args) ->
    let* (gma, pd, typ') = raw_check_coh tele typ in
    let* args' = raw_check_args args gma in
    raw_ok (CohT (pd,typ',args'), subst_ty args' typ')
    
and raw_check_args sub gma =
  match (sub,gma) with
  | (Ext (_,_), Emp) -> raw_fail "Too many arguments!"
  | (Emp, Ext (_,_)) -> raw_fail "Not enough arguments!"
  | (Emp, Emp) -> raw_ok Emp
  | (Ext (sub',tm), Ext (gma',typ)) ->
    let* rsub = raw_check_args sub' gma' in
    let typ' = subst_ty rsub typ in
    let* rtm = raw_check_tm tm typ' in
    raw_ok (Ext (rsub, rtm))

(* run the computation m in the context extended
 * by the telescope, checking as one goes that
 * the telescope is valid *)
      
(* and raw_with_tele tele m =  *)
and raw_with_tele : 'a. tele -> 'a RawMnd.m -> 'a RawMnd.m =
  fun tele m -> 
  match tele with
  | Emp -> m  (* Don't reset at the top of a new telescope *)
    (* let* env = tc_env in
     * tc_with_env { env with gma = Emp ; tau = Emp } m *)
  | Ext (tele',(id,typ)) -> 
    raw_with_tele tele'
      (let* typ' = raw_check_ty typ in
       let* d = raw_run_tc (tc_depth) in
       let* (renv, tenv) = raw_complete_env in 
       let tenv' = { tenv with gma = Ext (tenv.gma, typ') } in
       let renv' = { renv with tau = Ext (renv.tau, (id,d)) } in
       raw_with_env renv' tenv' m)

and raw_check_coh tele typ = 
  raw_with_tele tele
    (let* typ' = raw_check_ty typ in
     let* gma = raw_run_tc (tc_ctx) in
     (* printf "Telescope: %a@," pp_print_ctx gma; *)
     let* pd = raw_run_tc (tc_from_str_err (ctx_to_pd gma)) in
     let* _ = raw_run_tc (tc_check_is_full pd typ') in
     raw_ok (gma, pd, typ'))

and raw_pd_infer_args pd args_map =
  let module ST = SuiteTraverse(MndToApp(RawMnd)) in
  match pd with
  | Br (l,Emp) ->
    let arg = assoc l args_map in
    let* (arg_tm, arg_typ) = raw_infer_tm arg in 
    raw_ok (arg_typ, Br (arg_tm,Emp))
  | Br (_,brs) ->
    let lcl (_,b) = 
      let* (arg_typ, arg_br) = raw_pd_infer_args b args_map in
      (match arg_typ with
       | ObjT -> raw_fail "argument inference error"
       | ArrT (typ,src,tgt) ->
         raw_ok (typ,src,(tgt,arg_br))) in

    (* Finish this ... *)
    let* branch_results = ST.traverse lcl brs in
    let (t,s,_) = first branch_results in
    let branches = Suite.map (fun (_,_,b) -> b) branch_results in
    raw_ok (t, Br(s,branches))
    
let raw_check_term_decl tele ty tm =
  raw_with_tele tele 
    (let* gma = raw_run_tc (tc_ctx) in
     let* ty' = raw_check_ty ty in
     let* tm' = raw_check_tm tm ty' in
     raw_ok (gma,ty',tm'))

let raw_check_sig_decl tele ty =
  raw_with_tele tele
    (let* gma = raw_run_tc (tc_ctx) in
     let* ty' = raw_check_ty ty in
     raw_ok (gma, ty'))

(*****************************************************************************)
(*                            Sectioning Mechanism                           *)
(*****************************************************************************)

type decl =
  | TermDecl of (string * tele * ty_expr * tm_expr)
  | SigDecl of (string * tele * ty_expr)

(* Enter the section given by the telescope *)
let raw_in_section tele m =
  raw_with_tele tele (
    let* (renv, tenv) = raw_complete_env in
    let sec_args = Suite.map (fun (v,_) -> VarE v) renv.tau in
    let renv' = { renv with section_ids = [] ; section_args = sec_args } in 
    raw_with_env renv' tenv m 
  )

(* Check the list of declarations in the current section, adding
   each to the list of active section ids *)
let rec raw_check_section_decls decls =
  match decls with
  | [] ->
    let* (renv, tenv) = raw_complete_env in
    raw_ok (renv, tenv, [])
  | TermDecl(id,tele,ty,tm)::ds ->
    let* (renv, tenv, defs) = raw_check_section_decls ds in
    (* printf "-----------------@,";
     * printf "Checking section term declaration %s@," id; *)
    let* (gma, ty', tm') = raw_catch (raw_with_env renv tenv (raw_check_term_decl tele ty tm))
        (fun s -> raw_fail (sprintf "%s@,@,while checking the declaration %s" s id)) in 
    let tenv' = { tenv with rho = Ext (tenv.rho, (id, TCTermDef (gma,ty',tm'))) } in
    let renv' = { renv with section_ids = id::renv.section_ids } in
    (* printf "Ok!@,"; *)
    raw_ok (renv', tenv', (id,TCTermDef (gma,ty',tm'))::defs)
  | SigDecl(id,tele,ty)::ds ->
    let* (renv, tenv, defs) = raw_check_section_decls ds in
    (* printf "-----------------@,";
     * printf "Checking section signature declaration %s@," id; *)
    let* (_, _) = raw_catch (raw_with_env renv tenv (raw_check_sig_decl tele ty))
        (fun s -> raw_fail (sprintf "%s@,@,while checking the signature %s" s id)) in
    (* printf "Ok!@,"; *)
    raw_ok (renv, tenv, defs)
    
