(*****************************************************************************)
(*                                                                           *)
(*                                   Lexer                                   *)
(*                                                                           *)
(*****************************************************************************)

open Parser
    
let letter = [%sedlex.regexp? 'a'..'z'|'A'..'Z'] 
let space = [%sedlex.regexp? ' ' | '\t' | '\r']
let digit = [%sedlex.regexp? '0'..'9']
let number = [%sedlex.regexp? Plus digit]
let ident = [%sedlex.regexp? letter, Star ('A'..'Z' | 'a' .. 'z' | '_' | '-' | digit)]

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
  | "cylcoh"     -> CYLCOH 
  | "->"         -> ARROW 
  | "=>"         -> DBLARROW 
  | "("          -> LPAR 
  | ")"          -> RPAR 
  | "{"          -> LBR 
  | "}"          -> RBR 
  | "["          -> LBRKT 
  | "]"          -> RBRKT 
  | "cyl"        -> CYL 
  | "base"       -> BASE 
  | "lid"        -> LID 
  | "core"       -> CORE 
  | "|>"         -> BARARROW 
  | ":"          -> COLON 
  | "::"         -> DBLCOLON 
  | "="          -> EQUAL 
  | "."          -> DOT 
  | "\\"         -> LAMBDA 
  | "_"          -> HOLE 
  | "|"          -> VBAR 
  | "U"          -> TYPE 
  | "Arr"        -> ARR  
  | "Cat"        -> CAT 

  | ident -> IDENT (Sedlexing.Latin1.lexeme buf)
  | number -> INT (Base.Int.of_string (Sedlexing.Latin1.lexeme buf))

  | Plus space -> token buf
  | "#",Star (Compl '\n') -> token buf 
  | "\n" -> token buf (* Sedlexing.new_line buf ; token buf  *)
  | eof -> EOF
  | _ -> lexing_error buf (Printf.sprintf "Unexpected character \'%s\'" (Sedlexing.Latin1.lexeme buf))

