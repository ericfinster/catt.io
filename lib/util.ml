(*
 * util.ml - utility routines, especially for top-level
 *)

(* Some toplevel parsing routines ... *)
let parse_cell s =
  let lexbuf = Lexing.from_string s in
  Parser.raw_cell Lexer.token lexbuf

     
