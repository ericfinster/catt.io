(*
 * Routines for term wrangling
 *)

open Common
open Syntax

(* Given a term over a context, obtain its source or target *)
(*? What to do with 0-dimensional terms ?*)
let tm_ctx_src ( tm : tm_term) ( c : ctx ) : tm_term err = Fail "Not implemented"
let tm_ctx_tgt ( tm : tm_term) ( c : ctx ) : tm_term err = Fail "Not implemented"

(* Given a term over a context, determine if it is well-defined *)
let tm_ctx_ok ( tm : tm_term ) ( c : ctx ) : bool err = Fail "Not implemented"

(* Check if two terms are equal *)
let tm_eq tm1 tm2 = false (* Not implemented *)

(* Get the identity for a given term of a given type *)
let tm_get_id ( ty : ty_term) ( tm : tm_term ) : tm_term err = Fail "Not implemented"

(* Get the context D_n *)
let ctx_disk ( n : int ) : ctx err = Fail "Not implemented"

(* Given a context, give its variables as a list of terms *)
let ctx_var_list ( c : ctx ) : tm_term list =
  List.map (fun (s, _) -> VarT s) c

(* Given a pasting context, get the term which is its unbiased composite *)
let ctx_unbiased ( c : ctx ) : tm_term err = Fail "Not implemented"

(* Analyze a term to see if it is an endomorphism
   coherence at the cell level *)
let tm_endo_coh (tm : tm_term) : bool =
  match tm with
  | CellAppT(CohT(_, ArrT(_, src, tgt)), _) -> (tm_eq src tgt)
  | _ -> false
