(*****************************************************************************)
(*                                                                           *)
(*                                   Main                                    *)
(*                                                                           *)
(*****************************************************************************)

(* fix this .... *)
open Format

open Catt.Io
open Catt.Reduction

module W = Catt.Typecheck.Make(Weak)
module SU = Catt.Typecheck.Make(StrictUnit.Rec)
module SUA = Catt.Typecheck.Make(StrictUnitAssoc.Rec)

(*****************************************************************************)
(*                                  Options                                  *)
(*****************************************************************************)

let usage = "catt [options] [file]"

let strict_su = ref false
let strict_sua = ref false

let spec_list = [
    ("--su", Arg.Set strict_su, "Enable strictly unital normalisation");
    ("--sua", Arg.Set strict_sua, "Enable strictly unital and associative normalisation")
  ]

(*****************************************************************************)
(*                              Main Entry Point                             *)
(*****************************************************************************)

let () =
  let file_in = ref [] in
  set_margin 200;
  Arg.parse spec_list (fun s -> file_in := s::!file_in) usage;
  let files = List.rev (!file_in) in
  let defs = parse_all files in
  if !strict_sua then SUA.run_tc (SUA.check_defs SUA.empty_ctx defs)
  else if !strict_su then SU.run_tc (SU.check_defs SU.empty_ctx defs)
  else W.run_tc (W.check_defs W.empty_ctx defs)
