%{

    open Expr 
    open Suite
       
%} 

%token LET COH
%token TYPE CAT ARR
%token LAMBDA COLON DBLCOLON EQUAL DOT
%token LPAR RPAR LBR RBR LBRKT RBRKT QUOTBRKT
%token VBAR DBLARROW ARROW HOLE
%token CYL BASE CORE LID
%token SCOMP PCOMP
%token <string> IDENT
%token <int> INT
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
  | COH id = IDENT tl = tele COLON c = expr
    { CohDef (id,tl,c) }

/* Add separators and so on ... */
suite(X):
  | { Emp }
  | s = suite(X) x = X
    { Ext (s,x) }

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
  | LBR id = IDENT DBLCOLON c = expr RBR
    { (id,Impl,ObjE c) }

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
  | c = expr VBAR s = expr1 DBLARROW t = expr1
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
  | u = expr2 LBR v = expr2 RBR
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
  | BASE e = expr3
    { BaseE e }
  | LID e = expr3
    { LidE e }
  | CORE e = expr3
    { CoreE e }
  | CYL b = expr3 l = expr3 c = expr3
    { CylE (b,l,c) }
  | ARR c = expr3
    { ArrE c }
  | c = quot_cmd
    { QuotE c } 
  | LPAR t = expr RPAR
    { t }

paren_pd:
  | LPAR brs = suite(paren_pd) RPAR
    { ((),Pd.Br ((),brs)) }

quot_cmd:
  | QUOTBRKT PCOMP pd = paren_pd RBRKT
    { PComp (snd pd) }
  | QUOTBRKT SCOMP ds = INT+ RBRKT
    { SComp ds }
