(*
 * Term normalization
 *)

open Term
open Typecheck
open TcmMonad
    
(* Remove the first cell of a pasting context,
   necessarily locally maximal, and remove a
   further portion of the context, to reveal
   the next locally maximum cell *)
let rec remove_first_cell ( pd : ctx ) : ctx =
  match pd with
  | [] -> []
  | (_, _) :: [] -> []
  | (_, head_ty) :: (sec_id, sec_ty) :: tail ->
    if (dim_of(sec_ty) > dim_of(head_ty)) then
      (sec_id, sec_ty) :: tail
    else
      remove_first_cell ((sec_id, sec_ty) :: tail)

(* Get the locally maximal variables in a context *)
let rec locally_maximal ( pd : ctx ) : string list =
  match pd with
  | [] -> []
  | (head_id, _) :: _ -> head_id :: (locally_maximal (remove_first_cell pd))

(* Given the argument list for a cell, extract
   the argument corresponding to a given variable *)
(* let rec select_argument (c: ctx) args var = *)
(*   match c, args with *)
(*   | (id1,_)::tail1, el2::tail2 -> *)
(*     if (id1 = var) then *)
(*       el2 *)
(*     else *)
(*       select_argument tail1 tail2 var *)


(* Input: a term promisd to be an endomorphism coherence at the cell level
   Output: a term of dimension one higher, whose source is the input term,
           and whose target is the canonical parallel identity coherence *)
let tc_coh_endo_to_id (tm : tm_term) : tm_term tcm =
  match tm with
  | CellAppT(CohT(pd, ArrT(in_ty, in_src, in_tgt)), args) ->
     tc_eq_nf_tm in_src in_tgt >>= fun nf_match ->
     if (not nf_match) then 
       tc_fail "Source and target of coherence do not match"
     else (*
           * Here we construct the coherence
           *   [coh P: (coh P:tm->tm)[id] -> id_{tm}][s]
           * which should have type
           *   (coh P: tm -> tm)[s] --> (id_{tm})[s]
           *)
       tc_tm_get_id in_src >>= fun id_tm ->
       let typ = ArrT(in_ty, in_src, in_tgt) in 
       let old_coh = CohT (pd, typ) in
       let coh_between = CohT (pd, ArrT (typ, CellAppT (old_coh, id_args pd), id_tm)) in 
       tc_ok (CellAppT (coh_between, args))
  | _ -> tc_fail "Not an endo-coherence"
