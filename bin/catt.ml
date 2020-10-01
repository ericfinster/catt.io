(* 
 * catt.ml - top level catt module
 *)

open Format

open Catt.Command
open Catt.Typecheck
open Catt.Rawcheck

open Cheshire.Main
       
open MonadSyntax(RawMnd)

let usage = "catt [options] [file]"

let global_config = ref default_config

let enable_strict_units _ =
  printf "Using strictly unital normalization@,";
  global_config := { !global_config with norm_type = StrictlyUnital }

let spec_list = [
  ("-su", Arg.Unit enable_strict_units, "Enable strictly unital normalization")
]

let parse s =
  let lexbuf = Lexing.from_string s in
  try
    Catt.Parser.prog Catt.Lexer.token lexbuf
  with
  | Failure msg ->
    print_string msg;
    print_newline ();
    exit (-1)
  | Parsing.Parse_error ->
    print_string "Parse error";
    print_newline ();
    exit (-1)

let parse_file f =
  let sin =
    let fi = open_in f in
    let flen = in_channel_length fi in
    let buf = Bytes.create flen in
    really_input fi buf 0 flen;
    close_in fi;
    buf
  in parse (Bytes.to_string sin)

(* There has got to be a better way to pass the environment around ... *)
let rec raw_check_all files =
  match files with
  | [] -> raw_complete_env
  | f::fs ->
     let (impts, cmds) = parse_file f in
     let imprt_nms = List.map (fun fn -> fn ^ ".catt") impts in
     let* (renv, tenv) = raw_check_all imprt_nms in
     print_string "-----------------";
     print_cut ();
     printf "Processing input file: %s\n" f;
     let* (renv', tenv') = raw_with_env renv tenv (check_cmds cmds) in 
     raw_with_env renv' tenv' (raw_check_all fs)
  
let () =
  let file_in = ref [] in 
  open_vbox 0; (* initialize the pretty printer *)
  Arg.parse spec_list (fun s -> file_in := s::!file_in) usage;
  let files = List.rev (!file_in) in
  let tenv = { empty_env with config = !global_config } in 
  match raw_check_all files empty_raw_env tenv with
  | Ok _ ->
    printf "----------------@,Done";
    print_newline ()
  | Fail msg ->
    print_string "Failure:@,";
    print_string msg;
    print_cut ();
    print_string "----------------";
    print_newline ()


