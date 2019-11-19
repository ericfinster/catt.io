(*
 * Term normalization
 *)

open Common
open Syntax
let tc_fail msg _ = Fail msg

(* Get the locally maximal variables in a context *)
let rec locally_maximal ( pd : tele ) : string list =
  match pd with
(*| [] -> tc_fail "Empty pasting diagram"*)
  | (_, ObjE) :: [] -> []
  | (fill_id, fill_ty) :: (tgt_id, _) :: (src_id, _) :: pd' ->
    (* Is fill_id locally maximal? *)
    match fill_ty with
      | ObjE -> locally_maximal pd'
      | ArrE (fill_src, fill_tgt) ->
        match fill_src, fill_tgt with
          | VarE v_src, VarE v_tgt ->
            if ((v_src = src_id) || (v_tgt = tgt_id)) then
              locally_maximal pd' (* no, it's not *)
            else
              fill_id :: locally_maximal pd' (* yes, it is *)
          | _ -> locally_maximal pd'
  | _ -> []
