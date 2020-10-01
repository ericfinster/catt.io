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
    
open Cheshire.Main
       
open RawMnd
open MonadSyntax(RawMnd)
              
type cmd =
  | CohDef of string * tele * ty_expr
  | Decl of decl 
  | Section of tele * decl list
  | Prune of tele * tm_expr
  | Normalize of tele * tm_expr
  | Infer of tele * tm_expr

let rec check_cmds cmds =
  match cmds with
  | [] -> raw_complete_env

  | (CohDef (id, tele, typ)) :: ds -> 
    printf "-----------------@,";
    printf "Checking coh definition: %s@," id;
    printf "@[<hov>%a : %a@]@," pp_print_tele tele pp_print_expr_ty typ;
    let* (_,pd,typ') = raw_check_coh tele typ in 
    printf "Ok!@,";
    raw_with_coh id pd typ' (check_cmds ds)

  | (Decl (TermDecl (id, tele, ty, tm))) :: ds -> 
    printf "-----------------@,";
    printf "Checking term declaration: %s@," id;
    let* (gma,ty',tm') = raw_check_term_decl tele ty tm in
    printf "Ok!@,";
    raw_with_let id gma ty' tm' (check_cmds ds)

  | (Decl (SigDecl (id, tele, ty))) :: ds ->
    printf "-----------------@,";
    printf "Checking signature declaration: %s@," id;
    let* (_,_) = raw_check_sig_decl tele ty in
    check_cmds ds

  | (Section (tele, decls)) :: ds ->
    printf "-----------------@,";
    printf "Entering section ...@,";
    let* (_, _, defs) = raw_in_section tele
        (raw_check_section_decls (List.rev decls)) in
    let* (renv, tenv) = raw_complete_env in 
    let tenv' = { tenv with rho = Suite.append_list tenv.rho defs } in 
    printf "-----------------@,";
    printf "Finished section@,";
    raw_with_env renv tenv' (check_cmds ds)

  (* | (Prune (_, _)) :: _ -> raw_fail "help" *)
  | (Prune (tele, tm)) :: ds -> 
    printf "-----------------@,";
    printf "Pruning@,";
    let* _ = raw_with_tele tele
        (let* (tm',_) = raw_infer_tm tm in
         let* tm_nf = lift (tc_unfold_tm tm') in
         printf "Unfolded term:@,%a@," pp_print_tm tm_nf;
         match tm_nf with
         | CohT (pd,typ,args) ->
           let* (pd',typ',args') = lift (tc_lift (prune pd typ args)) in
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
         let* tm_nf = lift (tc_normalize_tm ~debug:true tm') in
         let expr_nf = term_to_expr_tm tm_nf in 
         printf "Normalized term:@,@[<hov>%a@]@," pp_print_expr_tm expr_nf;
         raw_ok ()) in 
    check_cmds ds

  (* | (Infer (_, _)) :: _ -> raw_fail "help" *)
  | (Infer (tele, tm)) :: ds ->
    printf "-----------------@,";
    printf "Inferring@,";
    printf "Expr: @[<hov>%a@]@," pp_print_expr_tm tm; 
    let* _ = raw_with_tele tele
        (let* (_,typ) = raw_infer_tm tm in
         let typ_expr = term_to_expr_ty typ in 
         printf "Inferred type:@,@[<hov>%a@]@," pp_print_expr_ty typ_expr;
         raw_ok ()) in 
    check_cmds ds


