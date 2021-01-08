(*****************************************************************************)
(*                                                                           *)
(*                                   Main                                    *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Catt.Io
open Catt.Typecheck
open Catt.Rawcheck       
       
let () = 
  let file_in = ref [] in
  pp_set_margin std_formatter 200;
  open_vbox 0; (* initialize the pretty printer *)
  Arg.parse spec_list (fun s -> file_in := s::!file_in) usage;
  let files = List.rev (!file_in) in
  let tenv = { empty_env with config = !global_config } in
  match raw_check_all files empty_raw_env tenv with
  | Ok (Ok _) ->
    printf "----------------@,Success!";
    print_newline ();
    print_newline ()
  | Fail terr ->
    printf "----------------@,Typing error:@,@,%s" (print_tc_err terr);
    print_cut ();
    print_newline ();
    print_newline ()
  | Ok (Fail s) ->
    printf "----------------@,Typing error:@,@,%s" s;
    print_cut ();
    print_newline ();
    print_newline ()


