(*
 * Term normalization
 *)

open Printf
open Common
open Syntax
let tc_fail msg _ = Fail msg

(* Get the locally maximal variables in a context *)
let rec locally_maximal ( pd : tele ) : string list =
  match pd with
  | [] -> []
  | (id, ObjE) :: [] -> [id]
  | (fill_id, fill_ty) :: (tgt_id, tgt_ty) :: (src_id, src_ty) :: pd' ->
    match fill_ty with
      (*| ObjE -> locally_maximal pd'*)
      | ArrE (fill_src, fill_tgt) ->
        if (dim_of src_ty = dim_of fill_ty) then
          fill_id :: locally_maximal ((src_id, src_ty) :: pd')
        else
          fill_id :: locally_maximal pd'
          (*
        match fill_src, fill_tgt with
          | VarE v_src, VarE v_tgt ->
            printf "** %s, %s, %s" fill_id v_src v_tgt;
            if ((v_src = src_id) || (v_tgt = tgt_id)) then
              locally_maximal pd' (* no, it's not *)
            else
              fill_id :: locally_maximal pd' (* yes, it is *)
          | _ -> locally_maximal pd'
          *)
  | _ -> []
