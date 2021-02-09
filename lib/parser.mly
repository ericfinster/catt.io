%{

    open Expr
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
%type <Expr.defn list> prog

%%

prog:
  | EOF
    { [] }
  | defs = nonempty_list(defn) EOF
    { defs }

defn:
  | LET id = IDENT tl = tele COLON ty = expr EQUAL tm = expr
    { TermDef (id,tl,ty,tm) }
  | COH id = IDENT tl = tele COLON c = cat
    { CohDef (id,tl,ObjE c) }

tele:
  |
    { Emp }
  | t = tele v = var_decl
    { Ext (t, v) }

var_decl:
  | LPAR id = IDENT COLON ty = expr RPAR
    { (id,ty) }
  | LPAR id = IDENT DBLCOLON c = cat RPAR
    { (id,ObjE c) }

expr:
  | e = expr1
    { e }
  | LAMBDA id = IDENT DOT e = expr1
    { LamE (id,e) }
  | LPAR id = IDENT COLON ty = expr1 RPAR ARROW tm = expr1
    { PiE (id,ty,tm) } 

expr1:
  | e = expr2
    { e }
  | e1 = expr1 e2 = expr2
    { AppE (e1,e2) }

expr2:
  | TYPE
    { TypE }
  | CAT
    { CatE } 
  | id = IDENT
    { VarE id }
  | LBRKT c = cat RBRKT
    { ObjE c }
  | LPAR e = expr RPAR
    { e }

cat:
  | id = IDENT
    { VarE id }
  | c = cat VBAR s = expr ARROW t = expr
    { HomE (Some c,s,t) }
  | s = expr ARROW t = expr
    { HomE (None,s,t) }
