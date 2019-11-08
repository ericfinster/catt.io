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

let check_file f =
  let s = Node.Fs.readFileAsUtf8Sync f in 
  match check_cmds (parse s) empty_env with
  | Succeed () -> print_endline "Finished"
  | Fail msg -> Printf.printf "Typechecking error: %s\n" msg ; exit (-1)
   
let () =
  let file_in = ref []
  in Arg.parse [] (fun s -> file_in := s::!file_in) usage;
  match !file_in with
  | f :: _ -> Printf.printf "Processing input file: %s\n" f ;
              check_file f
  | _ -> ()



