%{

    open Syntax
    open Suite
       
%} 

%token LET COH
%token TYPE CAT
%token LAMBDA COLON DBLCOLON EQUAL DOT
%token LPAR RPAR LBR RBR LBRKT RBRKT
%token VBAR DBLARROW ARROW HOLE
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
  | COH id = IDENT tl = tele COLON c = expr
    { CohDef (id,tl,c) }

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
  | LPAR id = IDENT DBLCOLON c = expr RPAR
    { (id,Expl,ObjE c) }

pi_head:
  | v = var_decl
    { v }
  | e = expr2
    { ("",Expl,e) }

expr: 
  | e = expr1
    { e }
  | s = expr1 DBLARROW t = expr1
    { HomE (HoleE,s,t) }
  | c = expr1 VBAR s = expr1 DBLARROW t = expr1
    { HomE (c,s,t) }
  | COH LBRKT tl = tele COLON e = expr RBRKT
    { CohE (tl,e) } 

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
  | CAT
    { CatE }
  | HOLE
    { HoleE } 
  | id = IDENT
    { VarE id }
  | LBRKT c = expr RBRKT
    { ObjE c }
  | LPAR t = expr RPAR
    { t }

