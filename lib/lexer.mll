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

rule token = parse

  | "let"        { LET }
  | "coh"        { COH }
  | "import"     { IMPRT }
  | "prune"      { PRUNE }
  | "normalize"  { NORMALIZE }
  | "infer"      { INFER }
  | "eqnf"       { EQNF }
  | "section"    { SECTION }
  | "where"      { WHERE } 
  | "end"        { END }
  | "sig"        { SIG }
  | "->"         { ARROW }
  | "*"          { OBJ }
  | "("          { LPAR }
  | ")"          { RPAR }
  | "["          { LBRACKET }
  | "]"          { RBRACKET }
  | ":"          { COLON }
  | ","          { COMMA }
  | "="          { EQUAL }
  | "|"          { VBAR }

  (* Identifiers *)
  | (['a'-'z''A'-'Z''0'-'9']['a'-'z''A'-'Z''0'-'9''_']* as str) { IDENT str }

  (* Comment and layout *)
  | space+                   { token lexbuf }
  | "#"[^'\n']*              { token lexbuf }
  | "\n"                     { Lexing.new_line lexbuf; token lexbuf }
  | eof                      { EOF }
  | _ as bad_char            { lexing_error lexbuf (Printf.sprintf "unexpected character \'%c\'" bad_char) }
  