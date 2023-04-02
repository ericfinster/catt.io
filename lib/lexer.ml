(*****************************************************************************)
(*                                                                           *)
(*                                   Lexer                                   *)
(*                                                                           *)
(*****************************************************************************)

open Parser

let space = [%sedlex.regexp? ' ' | '\t' | '\r']
let digit = [%sedlex.regexp? '0'..'9']
let number = [%sedlex.regexp? Plus digit]

(* lower lambda is reserved ... *)
let greek_lower = [%sedlex.regexp? 0x3B1 .. 0x3BA | 0x3BC .. 0x3C9]
let greek_upper = [%sedlex.regexp? 0x391 .. 0x3A9]
let subscripts = [%sedlex.regexp? 0x2080 .. 0x208E | 0x2090 .. 0x209C ]

let letter = [%sedlex.regexp? 'a'..'z'|'A'..'Z'|greek_lower|greek_upper]
let ident = [%sedlex.regexp? letter, Star (letter | subscripts | '_' | '-' | digit)]

exception Lexing_error of ((int * int) option * string)

let get_lexing_position lexbuf =
  let (p,_) = Sedlexing.lexing_positions lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)

let lexing_error lexbuf msg =
  let line, column = get_lexing_position lexbuf in
  raise (Lexing_error (Some (line, column), msg))

let rec token buf =
  match%sedlex buf with

  | "let"        -> LET
  | "coh"        -> COH
  | "ucomp"      -> UCOMP
  | "normalize"  -> NORMALIZE
  | "assert"     -> ASSERT
  | "->"         -> ARROW
  | "=>"         -> DBLARROW
  | "("          -> LPAR
  | ")"          -> RPAR
  | "{"          -> LBR
  | "}"          -> RBR
  | "["          -> LBRKT
  | "]"          -> RBRKT
  | "|>"         -> BARARROW
  | ":"          -> COLON
  | "::"         -> DBLCOLON
  | "="          -> EQUAL
  | "."          -> DOT
  | "\\"         -> LAMBDA
  | 0x03bb       -> LAMBDA
  | "_"          -> HOLE
  | "|"          -> VBAR
  | "U"          -> TYPE
  | "Arr"        -> ARR
  | "Cat"        -> CAT
  | "*"          -> STAR

  | ident -> IDENT (Sedlexing.Utf8.lexeme buf)
  | number -> INT (Base.Int.of_string (Sedlexing.Utf8.lexeme buf))

  | Plus space -> token buf
  | "#",Star (Compl '\n') -> token buf
  | "\n" -> token buf (* Sedlexing.new_line buf ; token buf  *)
  | eof -> EOF
  | _ -> lexing_error buf (Printf.sprintf "Unexpected character: %s" (Sedlexing.Utf8.lexeme buf))
