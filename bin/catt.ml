(* 
 * catt.ml - top level catt module
 *)

open Catt.Expr
open Catt.Typecheck
open Cheshire.Err
       
open TcmMonad

let usage = "catt [options] [file]"

let parse s =
  let lexbuf = Lexing.from_string s in
  try
    Catt.Parser.prog Catt.Lexer.token lexbuf
  with
  | Failure msg -> print_endline msg; exit (-1)
  | Parsing.Parse_error -> print_endline "Parse error"; exit (-1)

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
  | [] -> tc_get_env
  | f::fs ->
     (* let s = Node.Fs.readFileAsUtf8Sync f in *)
     let (impts, cmds) = parse_file f in
     let imprt_nms = List.map (fun fn -> fn ^ ".catt") impts in 
     tc_check_all imprt_nms >>= fun env -> 
     Printf.printf "-----------------\n";
     Printf.printf "Processing input file: %s\n" f;
     tc_with_env env (check_cmds cmds) >>= fun env' ->
     tc_with_env env' (tc_check_all fs)
     
let () =
  let file_in = ref []
  in Arg.parse [] (fun s -> file_in := s::!file_in) usage;
     let files = List.rev (!file_in) in 
     (* let files = List.tl (List.rev (!file_in)) in *)
     match tc_check_all files empty_env with
     | Ok _ -> print_endline "-----------------\nFinished"
     | Fail msg -> Printf.printf "Typechecking error: %s\n" msg ; exit (-1)
       
     

