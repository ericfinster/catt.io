(*****************************************************************************)
(*                                                                           *)
(*                                  Commands                                 *)
(*                                                                           *)
(*****************************************************************************)

open Expr
open Term

open Printf

open TcMonad.MonadSyntax
       
type cmd =
  | CellDef of string * tele * ty_expr
  | TermDef of string * tele * ty_expr * tm_expr
               
  (* | EqNf of tele * tm_expr * tm_expr
   * | Prune of tele * tm_expr
   * | Rectify of tele * tm_expr
   * | Normalize of tele * tm_expr
   * | LocMax of tele *)

let rec check_cmds cmds =
  match cmds with
  | [] -> tc_env 
  | (CellDef (id, _, _)) :: ds ->
     printf "-----------------\n";
     printf "Checking cell: %s\n" id;
     (* tc_check_cell_expr cell >>= fun cell_tm ->
      * printf "Ok!\n";
      * tc_with_cell id cell_tm (check_cmds ds) *)
     let* env = check_cmds ds in 
     tc_ok env
  | (TermDef (id, _, _, _)) :: ds ->
     printf "-----------------\n";
     printf "Checking definition: %s\n" id;
     (* tc_check_tele tele >>= fun g ->
      * printf "Valid telescope: %s\n" (print_term_ctx g);
      * tc_in_ctx g (tc_check_ty_expr typ) >>= fun typ_tm ->
      * printf "Valid return type: %s\n" (print_ty_term typ_tm);
      * tc_in_ctx g (tc_check_tm_expr tm typ_tm) >>= fun tm_tm ->
      * printf "Valid definition: %s\n" (print_tm_term tm_tm);
      * tc_with_def id g typ_tm tm_tm (check_cmds ds) *)
     let* env = check_cmds ds in
     tc_ok env 
