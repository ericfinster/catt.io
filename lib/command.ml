(*****************************************************************************)
(*                                                                           *)
(*                                  Commands                                 *)
(*                                                                           *)
(*****************************************************************************)

open Expr
open Term

open Format

open TcMonad.MonadSyntax
       
type cmd =
  | CellDef of string * tele * ty_expr
  | TermDef of string * tele * ty_expr * tm_expr
  | Prune of tele * tm_expr

let rec check_cmds cmds =
  match cmds with
  | [] -> tc_env 
  | (CellDef (id, tele, typ)) :: ds -> 
    printf "-----------------@,";
    printf "Checking coh definition: %s@," id;
    printf "@[<hov>%a : %a@]@," pp_print_tele tele pp_print_expr_ty typ;
    let* (_,pd,typ') = expr_tc_check_coh tele typ in 
    printf "Ok!@,";
    tc_with_coh id pd typ' (check_cmds ds)
  | (TermDef (id, tele, ty, tm)) :: ds -> 
    printf "-----------------@,";
    printf "Checking let definition: %s@," id;
    let* (gma,ty',tm') = expr_tc_in_tele tele 
        (let* gma = tc_ctx in
         let* ty' = expr_tc_check_ty ty in
         let* tm' = expr_tc_check_tm tm ty' in
         tc_ok (gma,ty',tm')) in
    printf "Ok!@,";
    tc_with_let id gma ty' tm' (check_cmds ds)
  | (Prune (tele, tm)) :: ds ->
    printf "-----------------@,";
    printf "Pruning@,";
    let* _ = expr_tc_in_tele tele
        (let* (tm',_) = expr_tc_infer_tm tm in
         let* tm_nf = tc_unfold_tm tm' in
         printf "Unfolded term:@,%a@," pp_print_tm tm_nf;
         match tm_nf with
         | CohT (pd,typ,args) ->
           let* (pd',typ',args') = tc_lift (prune pd typ args) in
           printf "Result:@,%a@," pp_print_tm (CohT (pd',typ',args'));
           tc_ok ()
         | _ ->
           printf "Normal form was not a coherence@,";
           tc_ok ()) in 
    
    check_cmds ds

