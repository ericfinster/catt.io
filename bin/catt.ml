(* 
 * catt.ml - top level catt module
 *)

open Format

open Catt.Term
open Catt.Command
       
open Cheshire.Err
       
open TcMonad.MonadSyntax

let usage = "catt [options] [file]"

let enable_strict_units _ =
  printf "Using strictly unital normalization@,";
  norm_opt := StrictlyUnital
    
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
                           
let rec tc_check_all files =
  match files with
  | [] -> tc_env
  | f::fs ->
     let (impts, cmds) = parse_file f in
     let imprt_nms = List.map (fun fn -> fn ^ ".catt") impts in
     let* env = tc_check_all imprt_nms in
     print_string "-----------------";
     print_cut ();
     printf "Processing input file: %s\n" f;
     let* env' = tc_with_env env (check_cmds cmds) in 
     tc_with_env env' (tc_check_all fs)
  
let () =
  let file_in = ref [] in 
  open_vbox 0; (* initialize the pretty printer *)
  Arg.parse spec_list (fun s -> file_in := s::!file_in) usage;
  let files = List.rev (!file_in) in 
  match tc_check_all files empty_env with
  | Ok _ ->
    printf "----------------@,Done";
    print_newline ()
  | Fail msg ->
    print_string "Failure:@,";
    print_string msg;
    print_cut ();
    print_string "----------------";
    print_newline ()


