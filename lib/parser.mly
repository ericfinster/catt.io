%{

    open Syntax
    open Suite
       
%} 

%token LET COH
%token TYPE 
%token COLON EQUAL
%token LPAR RPAR
%token COMMA ARROW
%token <string> IDENT 
%token EOF

%start prog
%type <Syntax.defn list> prog

%%

prog:
  | EOF
    { [] }
  | defs = nonempty_list(defn) EOF
    { defs }

defn:
  | LET id = IDENT tl = tele COLON ty = expr EQUAL tm = expr
    { TermDef (id,tl,ty,tm) }
  | COH id = IDENT tl = tele COLON ty = expr
    { CohDef (id,tl,ty) }

tele:
  |
    { Emp }
  | t = tele v = var_decl
    { Ext (t, v) }

var_decl:
  | LPAR id = IDENT COLON ty = expr RPAR
    { (id, ty) }

expr:
  | TYPE
    { TypE }
