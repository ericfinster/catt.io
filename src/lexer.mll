{
  open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse

  | "coh"        { COH }
  | "->"         { ARROW }
  | "*"          { OBJ }
  | "|"          { PIPE }
  | "("          { LPAR }
  | ")"          { RPAR }
  | ":"          { COLON }

  (* Identifiers *)
  | (['a'-'z''A'-'Z''0'-'9']['-''+''a'-'z''A'-'Z''0'-'9''_''@''{''}''/'',''\'']* as str) { IDENT str }

  (* Comment and layout *)
  | space+                   { token lexbuf }
  | "#"[^'\n']*              { token lexbuf }
  | "\n"                     { Lexing.new_line lexbuf; token lexbuf }
  | eof                      { EOF }
