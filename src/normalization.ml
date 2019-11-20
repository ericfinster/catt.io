(*
 * Term normalization
 *)

open Printf
open Common
open Syntax

(* Remove the first cell of a pasting context,
   necessarily locally maximal, to reveal the
   next locally maximum cell *)
let rec remove_first_cell ( pd : ctx ) : ctx =
  match pd with
  | [] -> []
  | (head_id, head_ty) :: [] -> []
  | (head_id, head_ty) :: (sec_id, sec_ty) :: tail ->
    if (dim_of(sec_ty) > dim_of(head_ty)) then
      (sec_id, sec_ty) :: tail
    else
      remove_first_cell ((sec_id, sec_ty) :: tail)

(* Get the locally maximal variables in a context *)
let rec locally_maximal ( pd : ctx ) : string list =
  match pd with
  | [] -> []
  | (head_id, head_ty) :: tail ->
    head_id :: (locally_maximal (remove_first_cell pd))
