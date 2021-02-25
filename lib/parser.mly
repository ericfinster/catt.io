%{

    open Syntax
    open Suite
       
%} 

%token LET
%token TYPE 
%token LAMBDA COLON EQUAL DOT
%token LPAR RPAR LBR RBR
%token ARROW HOLE
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
    { Def (id,tl,ty,tm) }

tele:
  |
    { Emp }
  | t = tele v = var_decl
    { Ext (t, v) }

var_decl:
  | LPAR id = IDENT COLON ty = expr RPAR
    { (id,Expl,ty) }
  | LBR id = IDENT COLON ty = expr RBR
    { (id,Impl,ty) }

pi_head:
  | v = var_decl
    { v }
  | e = expr2
    { ("",Expl,e) }

expr: 
  | e = expr1
    { e }

expr1:
  | e = expr2
    { e }
  | LAMBDA id = IDENT DOT e = expr1
    { LamE (id,Expl,e) }
  | LAMBDA LBR id = IDENT RBR DOT e = expr1
    { LamE (id,Impl,e) }
  | hd = pi_head ARROW cod = expr1
    { let (nm,ict,dom) = hd in PiE (nm,ict,dom,cod) }

expr2:
  | e = expr3
    { e }
  | u = expr2 LBR v = expr3 RBR
    { AppE (u,v,Impl) }
  | u = expr2 v = expr3
    { AppE (u,v,Expl) }

expr3:
  | TYPE
    { TypE }
  | HOLE
    { HoleE } 
  | id = IDENT
    { VarE id }
  | LPAR t = expr RPAR
    { t }

