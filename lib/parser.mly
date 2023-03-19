%{

    open Expr
    open Suite

%}

%token LET LAMBDA COLON DBLCOLON EQUAL DOT
%token LPAR RPAR LBR RBR LBRKT RBRKT
%token VBAR DBLARROW ARROW HOLE BARARROW
%token UCOMP COH NORMALIZE
%token TYPE CAT ARR STAR
%token <string> IDENT
%token <int> INT
%token EOF

%start prog
%type <Expr.defn list> prog

%start id_pd
%type <string Pd.pd> id_pd

%%

suite(X):
  | { Emp }
  | s = suite(X); x = X
    { Ext (s,x) }

prog:
  | EOF
    { [] }
  | defs = nonempty_list(defn) EOF
    { defs }

defn:
  | LET id = IDENT tl = tele COLON ty = expr EQUAL tm = expr
    { TermDef (id,tl,ty,tm) }
  | COH id = IDENT pd = pd_expr COLON cat = expr BARARROW src = expr1 DBLARROW tgt = expr1
    { CohDef (id,pd,cat,src,tgt) }
  | COH id = IDENT pd = pd_expr COLON src = expr1 DBLARROW tgt = expr1
    { CohDef (id,pd,HoleE,src,tgt) }
  | NORMALIZE tl = tele VBAR tm = expr
    { Normalize (tl,tm) }

var_decl:
  | LPAR id = IDENT COLON ty = expr RPAR
    { (id,Expl,ty) }
  | LBR id = IDENT COLON ty = expr RBR
    { (id,Impl,ty) }
  | LPAR id = IDENT DBLCOLON c = expr RPAR
    { (id,Expl,ObjE c) }
  | LBR id = IDENT DBLCOLON c = expr RBR
    { (id,Impl,ObjE c) }

tele:
  | tl = suite(var_decl)
    { tl }

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
  | coh = coh_expr
    { coh }
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
  | STAR
    { StarE }
  | id = IDENT
    { VarE id }
  | LBRKT c = expr RBRKT
    { ObjE c }
  | ARR c = expr3
    { ArrE c }
  | LPAR t = expr RPAR
    { t }

paren_pd:
  | LPAR brs = suite(paren_pd) RPAR
    { ((),Pd.Br ((),brs)) }

ucomp_pd:
  | pd = paren_pd
    { UnitPd (snd pd) }
  | ds = INT+
    { DimSeq ds }

pd_with_tgt:
  | pd = id_pd tgt = IDENT
    { (tgt,pd) }

id_pd:
  | LPAR src = IDENT brs = suite(pd_with_tgt) RPAR
    { Pd.Br (src,brs) }

pd_expr:
  | tl = tele
    { tl }
  | pd = id_pd
    { string_pd_to_expr_tele pd }

coh_expr:
  | UCOMP LBRKT upd = ucomp_pd RBRKT
    { UCompE upd }
  | COH LBRKT pd = pd_expr COLON cat = expr
      BARARROW src = expr1 DBLARROW tgt = expr1 RBRKT
    { CohE (pd,cat,src,tgt) }
