(* 
 * catt.ml - top level catt module
 *)

open Typecheck

let usage = "catt [options] [file]"

let parse s =
  let lexbuf = Lexing.from_string s in
  try
    Parser.prog Lexer.token lexbuf
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

let check_file f =
  match check_decls (parse_file f) [] with
  | Succeed () -> print_endline "Finished"
  | Fail msg -> Printf.printf "Typechecking error: %s" msg
   
let () =
  let file_in = ref []
  in Arg.parse [] (fun s -> file_in := s::!file_in) usage;
  match !file_in with
    | [f] -> check_file f
    | _ -> ()



