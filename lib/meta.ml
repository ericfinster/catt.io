(*****************************************************************************)
(*                                                                           *)
(*                               Metavariables                               *)
(*                                                                           *)
(*****************************************************************************)

open Base
open Syntax
open Value

type meta_entry =
  | Solved of value
  | Unsolved

type metamap = (mvar,meta_entry,Int.comparator_witness) Map.t

let next_meta : int ref = ref 0

let metacontext : metamap ref =
  ref (Map.empty (module Int))

exception Meta_error of string

let lookup_meta m =
  let mctx = ! metacontext in
  match Map.find mctx m with
  | Some mentry -> mentry
  | None -> raise (Meta_error "unrecognized metavariable")
