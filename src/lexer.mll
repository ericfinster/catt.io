{
  open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse

  | "let"        { LET }
  | "eqnf"       { EQNF }
  | "coh"        { COH }
  | "comp"       { COMP }
  | "locmax"     { LOCMAX }
  | "prune"      { PRUNE }
  | "rectify"    { RECTIFY }
  | "normalize"  { NORMALIZE }
  | "import"     { IMPORT } 
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
