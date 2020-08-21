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

let rec check_cmds cmds =
  match cmds with
  | [] -> tc_env 
  | (CellDef (id, tele, typ)) :: ds ->
    printf "-----------------@,";
    printf "Checking cell definition: %s@," id;
    printf "@[<hov>%a : %a@]@," pp_print_tele tele pp_print_expr_ty typ;
    let* _ = expr_tc_check_coh tele typ in 
    printf "Ok!@,";
      (* tc_with_cell id cell_tm (check_cmds ds) *)
    let* env = check_cmds ds in 
    tc_ok env
  | (TermDef (id, _, _, _)) :: ds ->
     printf "-----------------@,";
     printf "Checking definition: %s@," id;
     (* tc_check_tele tele >>= fun g ->
      * printf "Valid telescope: %s\n" (print_term_ctx g);
      * tc_in_ctx g (tc_check_ty_expr typ) >>= fun typ_tm ->
      * printf "Valid return type: %s\n" (print_ty_term typ_tm);
      * tc_in_ctx g (tc_check_tm_expr tm typ_tm) >>= fun tm_tm ->
      * printf "Valid definition: %s\n" (print_tm_term tm_tm);
      * tc_with_def id g typ_tm tm_tm (check_cmds ds) *)
     let* env = check_cmds ds in
     tc_ok env 
