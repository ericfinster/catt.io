%{

    open Syntax
    open Suite
       
%} 

%token LET COH
%token TYPE CAT
%token LAMBDA COLON DBLCOLON EQUAL DOT
%token LPAR RPAR LBRKT RBRKT
%token ARROW VBAR
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
  | LET id = IDENT tl = tele COLON ty = term EQUAL tm = term
    { TermDef (id,tl,ty,tm) }
  | COH id = IDENT tl = tele COLON c = cat
    { CohDef (id,tl,ObjT c) }

tele:
  |
    { Emp }
  | t = tele v = var_decl
    { Ext (t, v) }

var_decl:
  | LPAR id = IDENT COLON ty = term RPAR
    { (id,ty) }
  | LPAR id = IDENT DBLCOLON c = cat RPAR
    { (id,ObjT c) }

term:
  | e = term1
    { e }
  | LAMBDA id = IDENT DOT e = term
    { LamT (Some id,e) }
  | LPAR id = IDENT COLON ty = term RPAR ARROW tm = term
    { PiT (Some id,ty,tm) } 

term1:
  | e = term2
    { e }
  | e1 = term1 e2 = term2
    { AppT (e1,e2) }

term2:
  | TYPE
    { TypT }
  | CAT
    { CatT } 
  | id = IDENT
    { IdT id }
  | LBRKT c = cat RBRKT
    { ObjT c }
  | LPAR e = term RPAR
    { e }

cat:
  | id = IDENT
    { IdT id }
  | c = cat VBAR s = term ARROW t = term
    { HomT (Some c,s,t) }
  | s = term ARROW t = term
    { HomT (None,s,t) }
