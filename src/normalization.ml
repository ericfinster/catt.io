(*
 * Term normalization
 *)

open Term
open Typecheck

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
       let coh_between = CohT (pd, ArrT (typ, CellAppT (old_coh, id_sub pd), id_tm)) in 
       tc_ok (CellAppT (coh_between, args))
  | _ -> tc_fail "Not an endo-coherence"

(* Check if the given variable, promised to be locally
   maximal, can be pruned *)
(* Promise: term is a cell application *)
(* Promise: variable is locally maximal in the cell pd *)
(* let verify_prunable ( cell : cell_term ) ( v : string ) : bool = *)
(*   match cell with *)
(*   | (cell_tm, args) -> *)
(*     let pd = cell_pd cell in *)
(*     let arg = select_argument pd args v in *)
(*     (\* arg is a term. check if it's an identity *)
(*        coherence at the cell level *\) *)
(*     identity_coherence arg *)

(* To prune an endomorphism coherence we need to
   first apply a coherence to the identity, and
   then a second coherence which removes the
   argument.

   It's something like this at the argument level:

    
   Need to apply this to the particular argument,
   then prune. *)

(* Try to prune an argument from the cell,
   returning the pruned term, or else the
   original term *)
   (*
let prune ( tm : tm_term ) : tm_term =
  match tm with
  | VarT _ -> printf "Term is a variable, nothing to do\n"; tm
  | DefAppT _ -> printf "Term is a definition application, nothing to do\n"; tm
  | CellAppT (cell, args) ->

  *) 

