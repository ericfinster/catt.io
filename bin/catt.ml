(*****************************************************************************)
(*                                                                           *)
(*                                   Main                                    *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Catt.Io
open Catt.Syntax

(*****************************************************************************)
(*                                  Options                                  *)
(*****************************************************************************)
    
let usage = "catt [options] [file]"

let spec_list = []

(*****************************************************************************)
(*                              Main Entry Point                             *)
(*****************************************************************************)

let () = 
  let file_in = ref [] in
  pp_set_margin std_formatter 200;
  open_vbox 0; (* initialize the pretty printer *)
  Arg.parse spec_list (fun s -> file_in := s::!file_in) usage;
  let files = List.rev (!file_in) in
  let defs = parse_all files in
  try let _ = check_defs empty_ctx defs in
    printf "----------------@,Success!";
    print_newline ();
    print_newline ()
  with
  | Typing_error msg ->
    printf "Typing error: %s@," msg
  | Unify_error msg ->
    printf "Unification error: %s@," msg

