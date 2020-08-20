(*****************************************************************************)
(*                                                                           *)
(*                                  Commands                                 *)
(*                                                                           *)
(*****************************************************************************)

open Expr

type cmd =
  | CellDef of string * tele * ty_expr
  | TermDef of string * tele * ty_expr * tm_expr
               
  (* | EqNf of tele * tm_expr * tm_expr
   * | Prune of tele * tm_expr
   * | Rectify of tele * tm_expr
   * | Normalize of tele * tm_expr
   * | LocMax of tele *)

