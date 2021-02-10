(*****************************************************************************)
(*                                                                           *)
(*                                   Main                                    *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Catt.Io
open Catt.Syntax

let () = 
  let file_in = ref [] in
  pp_set_margin std_formatter 200;
  open_vbox 0; (* initialize the pretty printer *)
  Arg.parse spec_list (fun s -> file_in := s::!file_in) usage;
  let files = List.rev (!file_in) in
  let defs = parse_all files in
  match tc_check_defns defs empty_env with
  | Ok _ -> 
    printf "----------------@,Success!";
    print_newline ();
    print_newline ()
  | Fail terr -> 
    printf "----------------@,Typing error:@,@,%a"
      pp_print_tc_err terr;
    print_cut ();
    print_newline ();
    print_newline ()



