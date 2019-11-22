(*
 * Routines for term wrangling
 *)

open Common
open Term

(* Given a term over a context, obtain its source or target *)
(* EF - Done, see term source and target section of typecheck.ml *)
(*      Note: calling the functions on objects returns an error *)
(* let tm_ctx_src ( tm : tm_term) ( c : ctx ) : tm_term err = Fail "Not implemented" *)
(* let tm_ctx_tgt ( tm : tm_term) ( c : ctx ) : tm_term err = Fail "Not implemented" *)

(* Given a term over a context, determine if it is well-defined *)
(* EF - Done: use tc_check_tm *)
(* let tm_ctx_ok ( tm : tm_term ) ( c : ctx ) : bool err = Fail "Not implemented" *)

(* Check if two terms are equal *)
(* EF - Done: use tc_eq_nf_tm to compare up to simple normal forms *)
(* let tm_eq tm1 tm2 = false *)

(* Get the identity for a given term of a given type *)
(* EF - Done: tc_tm_get_id in typecheck.ml *)                  
(* let tm_get_id ( ty : ty_term) ( tm : tm_term ) : tm_term err = Fail "Not implemented" *)

(* Get the context D_n *)
(* EF - Done: see disc_pd in term.ml *)                                                             
(* let ctx_disk ( n : int ) : ctx err = Fail "Not implemented" *)

(* Given a context, give its variables as a list of terms *)
let ctx_var_list ( c : ctx ) : tm_term list =
  List.map (fun (s, _) -> VarT s) c

(* Given a pasting context, get the term which is its unbiased composite *)
(* EF - Done: see tc_ucomp in typcheck.ml *)
(* let ctx_unbiased ( c : ctx ) : tm_term err = Fail "Not implemented" *)

(* Analyze a term to see if it is an endomorphism
   coherence at the cell level *)
(* EF - Needs rewriting with above implementations *)
(* let tm_endo_coh (tm : tm_term) : bool = *)
(*   match tm with *)
(*   | CellAppT(CohT(_, ArrT(_, src, tgt)), _) -> (tm_eq src tgt) *)
(*   | _ -> false *)
