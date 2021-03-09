{

  open Parser

  exception Lexing_error of ((int * int) option * string)

  let get_lexing_position lexbuf =
    let p = Lexing.lexeme_start_p lexbuf in
    let line_number = p.Lexing.pos_lnum in
    let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
    (line_number, column)

  let lexing_error lexbuf msg =
    let line, column = get_lexing_position lexbuf in
    raise (Lexing_error (Some (line, column), msg))
    
}

let space = ' ' | '\t' | '\r'
let int = '-'? ['0'-'9'] ['0'-'9']*

rule token = parse

  | "let"        { LET }
  | "coh"        { COH }
  | "->"         { ARROW }
  | "=>"         { DBLARROW }
  | "("          { LPAR }
  | ")"          { RPAR }
  | "{"          { LBR }
  | "}"          { RBR }
  | "["          { LBRKT }
  | "]"          { RBRKT }
  | "`["         { QUOTBRKT }
  | "cyl"        { CYL }
  | "base"       { BASE }
  | "lid"        { LID }
  | "core"       { CORE }
  | "ucomp"      { UCOMP }
  | "compseq"    { COMPSEQ }
  | ":"          { COLON }
  | "::"         { DBLCOLON }
  | "="          { EQUAL }
  | "."          { DOT }
  | "\\"         { LAMBDA }
  | "_"          { HOLE }
  | "|"          { VBAR }
  | "U"          { TYPE }
  | "Arr"        { ARR } 
  | "Cat"        { CAT }

  (* Identifiers *)
  | (['a'-'z''A'-'Z''0'-'9']['a'-'z''A'-'Z''0'-'9''_']* as str) { IDENT str }

  (* Integers *)
  | int                      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  
  (* Comment and layout *)
  | space+                   { token lexbuf }
  | "#"[^'\n']*              { token lexbuf }
  | "\n"                     { Lexing.new_line lexbuf; token lexbuf }
  | eof                      { EOF }
  | _ as bad_char            { lexing_error lexbuf (Printf.sprintf "unexpected character \'%c\'" bad_char) }
  