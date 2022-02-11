(*****************************************************************************)
(*                                                                           *)
(*                                  Commands                                 *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Term
open Expr
open Typecheck
open Rawcheck

open Mtl

(* open RawMnd *)
open MonadSyntax(RawMnd)

type cmd =
  | CohDef of string * tele * ty_expr
  | Decl of decl
  | Section of tele * decl list
  | Prune of tele * tm_expr
  | Normalize of tele * tm_expr
  | Infer of tele * tm_expr
  | Eqnf of tele * tm_expr * tm_expr

let rec check_cmds cmds =
  match cmds with
  | [] -> raw_complete_env

  | (CohDef (id, tele, typ)) :: ds ->
    (* printf "-----------------@,"; *)
    (* printf "Checking coh definition: %s@," id; *)
    (* printf "@[<hov>%a : %a@]@," pp_print_tele tele pp_print_expr_ty typ; *)
    let* (_,pd,typ') = raw_catch (raw_check_coh tele typ)
        (fun s -> raw_fail (sprintf "%s@,@,while checking coherence %s" s id)) in
    (* printf "Ok!@,"; *)
    raw_with_coh id pd typ' (check_cmds ds)

  | (Decl (TermDecl (id, tele, ty, tm))) :: ds ->
    (* printf "-----------------@,"; *)
    (* printf "Checking definition: %s@," id; *)
    let* (gma,ty',tm') = raw_catch (raw_check_term_decl tele ty tm)
        (fun s -> raw_fail (sprintf "%s@,@,while checking the declaration %s" s id)) in
    (* printf "Ok!@,"; *)
    raw_with_let id gma ty' tm' (check_cmds ds)

  | (Decl (SigDecl (id, tele, ty))) :: ds ->
    (* printf "-----------------@,";
     * printf "Checking signature declaration: %s@," id; *)
    let* (_,_) = raw_catch (raw_check_sig_decl tele ty)
        (fun s -> raw_fail (sprintf "%s@,@,while checking the signature %s" s id)) in
    check_cmds ds

  | (Section (tele, decls)) :: ds ->
    (* printf "-----------------@,";
     * printf "Entering section ...@,"; *)
    let* (_, _, defs) = raw_in_section tele
        (raw_check_section_decls (List.rev decls)) in
    let* (renv, tenv) = raw_complete_env in
    let tenv' = { tenv with rho = Suite.append_list tenv.rho defs } in
    (* printf "-----------------@,";
     * printf "Finished section@,"; *)
    raw_with_env renv tenv' (check_cmds ds)

  (* | (Prune (_, _)) :: _ -> raw_fail "help" *)
  | (Prune (tele, tm)) :: ds ->
    printf "-----------------@,";
    printf "Pruning@,";
    let* _ = raw_with_tele tele
        (let* (tm',_) = raw_infer_tm tm in
         let* tm_nf = raw_run_tc (tc_unfold_tm tm') in
         printf "Unfolded term:@,%a@," pp_print_tm tm_nf;
         match tm_nf with
         | CohT (pd,typ,args) ->
           let* (pd',typ',args') = raw_run_tc (tc_from_str_err (prune pd typ args)) in
           printf "Result:@,%a@," pp_print_tm (CohT (pd',typ',args'));
           raw_ok ()
         | _ ->
           printf "Normal form was not a coherence@,";
           raw_ok ()) in

    check_cmds ds

  (* | (Normalize (_, _)) :: _ -> raw_fail "help" *)
  | (Normalize (tele, tm)) :: ds ->
    printf "-----------------@,";
    printf "Normalizing@,";
    printf "Expr: @[<hov>%a@]@," pp_print_expr_tm tm;
    let* _ = raw_with_tele tele
        (let* (tm',_) = raw_infer_tm tm in
         let* tm_nf = raw_run_tc (tc_normalize_tm ~debug:true tm') in
         let* renv = raw_env in
         let rev_var_map = Suite.map (fun (x,y) -> (y,x)) renv.tau in
         let var_lookup i =
           try VarE (Suite.assoc i rev_var_map)
           with Not_found -> VarE (sprintf "_x%d" i) in
         let expr_nf = term_to_expr_tm var_lookup tm_nf in
         printf "Normalized term:@,@[<hov>%a@]@," pp_print_expr_tm expr_nf;
         (* let expr_ast = ast_as_pd expr_nf in *)
         (* printf "Normalized ast:@,%a@," pp_print_ast expr_ast; *)
         raw_ok ()) in
    check_cmds ds

  (* | (Infer (_, _)) :: _ -> raw_fail "help" *)
  | (Infer (tele, tm)) :: ds ->
    printf "-----------------@,";
    printf "Inferring@,";
    printf "Expr: @[<hov>%a@]@," pp_print_expr_tm tm;
    let* _ = raw_with_tele tele
        (let* (_,typ) = raw_infer_tm tm in
         let typ_expr = term_to_expr_ty_default typ in
         printf "Inferred type:@,@[<hov>%a@]@," pp_print_expr_ty typ_expr;
         raw_ok ()) in
    check_cmds ds

  | (Eqnf (tele, tm_a, tm_b)) :: ds ->
    printf "-----------------@,";
    printf "Checking normal form equality between:@,";
    printf "Expr A: @[<hov>%a@]@," pp_print_expr_tm tm_a;
    printf "Expr B: @[<hov>%a@]@," pp_print_expr_tm tm_b;
    let* _ = raw_with_tele tele
        (let* (tm_a_tm, _) = raw_infer_tm tm_a in
         let* (tm_b_tm, _) = raw_infer_tm tm_b in
         let* tm_a_nf = raw_run_tc (tc_normalize_tm tm_a_tm) in
         let* tm_b_nf = raw_run_tc (tc_normalize_tm tm_b_tm) in
         if (tm_a_nf = tm_b_nf) then
           (printf "Terms have equal normal forms.@,"; raw_ok ())
         else
           (printf "Terms have different normal forms.@,"; raw_ok ())
        )
    in check_cmds ds
