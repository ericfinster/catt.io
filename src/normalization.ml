(*
 * Term normalization
 *)

open Syntax

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
  | (head_id, _) :: _ ->
    head_id :: (locally_maximal (remove_first_cell pd))

(* Given the argument list for a cell, extract
   the argument corresponding to a given variable *)
let rec select_argument (c: ctx) args var =
  match c, args with
  | (id1,_)::tail1, el2::tail2 ->
    if (id1 = var) then
      el2
    else
      select_argument tail1 tail2 var

(* Analyze a term to see if it is an identity
   coherence at the cell level *)
let identity_coherence (tm : tm_term) : bool =
  match tm with
  | CellAppT (cell, _) -> (
    match cell with
    | CohT (_, ty) -> (
      match ty with
      | ArrT (_, src, tgt) ->
        (src = tgt)
      | _ -> false
    )
    | _ -> false
  )
  | _ -> false
  

(* Check if the given variable, promised to be locally
   maximal, can be pruned *)
(* Promise: term is a cell application *)
(* Promise: variable is locally maximal in the cell pd *)
let verify_prunable ( cell : cell_term ) ( v : string ) : bool =
  match cell with
  | (cell_tm, args) ->
    let pd = cell_pd cell in
    let arg = select_argument pd args v in
    (* arg is a term. check if it's an identity
       coherence at the cell level *)
    identity_coherence arg

(* To prune an endomorphism coherence we need to
   first apply a coherence to the identity, and
   then a second coherence which removes the
   argument.

   It's something like this at the argument level:

    [coh P: (coh P:tm->tm)[id] -> id_{tm}][s]
    : (coh P: tm -> tm)[s] --> (id_{tm})[s]
    
   Need to apply this to the particular argument,
   then prune. *)

(* Try to prune an argument from the cell,
   returning the pruned term, or else the
   original term *)
let prune ( tm : tm_term ) : tm_term =
  match tm with
  | VarT _ -> printf "Term is a variable, nothing to do\n"; tm
  | DefAppT _ -> printf "Term is a definition application, nothing to do\n"; tm
  | CellAppT (cell, args) ->