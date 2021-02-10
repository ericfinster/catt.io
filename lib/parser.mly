%{

    open Syntax
    open Suite
       
%} 

%token LET COH
%token TYPE CAT
%token LAMBDA COLON DBLCOLON EQUAL DOT
%token LPAR RPAR LBRKT RBRKT
%token DBLARROW ARROW VBAR
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
  | COH id = IDENT tl = tele COLON c = term
    { CohDef (id,tl,ObjT c) }

tele:
  |
    { Emp }
  | t = tele v = var_decl
    { Ext (t, v) }

var_decl:
  | LPAR id = IDENT COLON ty = term RPAR
    { (id,ty) }
  | LPAR id = IDENT DBLCOLON c = term RPAR
    { (id,ObjT c) }

term: 
  | t = term1
    { t }
  | s = term1 DBLARROW t = term1
    { HomT (None,s,t) }
  | c = term1 VBAR s = term1 DBLARROW t = term1
    { HomT (Some c,s,t) }

term1:
  | t = term2
    { t }
  | LAMBDA id = IDENT DOT e = term1
    { LamT (Some id,e) }
  | LPAR id = IDENT COLON ty = term1 RPAR ARROW tm = term1
    { PiT (Some id,ty,tm) } 

term2:
  | t = term3
    { t }
  | u = term2 v = term3
    { AppT (u,v) }

term3:
  | TYPE
    { TypT }
  | CAT
    { CatT } 
  | id = IDENT
    { IdT id }
  | LBRKT c = term RBRKT
    { ObjT c }
  | LPAR t = term RPAR
    { t }

