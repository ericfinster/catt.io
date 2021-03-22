%{

    open Expr 
    open Suite
       
%} 

%token LET COH COMP UCOMP 
%token TYPE CAT ARR
%token LAMBDA COLON DBLCOLON EQUAL DOT
%token LPAR RPAR LBR RBR LBRKT RBRKT 
%token VBAR BARARROW IFF DBLARROW ARROW HOLE
%token CYL BASE CORE LID
%token <string> IDENT
%token <int> INT
%token EOF

%start prog
%type <Expr.defn list> prog

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
  /* | COMP id = IDENT pd = pd_expr COLON cat = expr BARARROW src = expr DBLARROW tgt = expr */
  /*   { CompDef (id,pd,cat,src,tgt) } */

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
  | ARR c = expr3
    { ArrE c }
  | BASE e = expr3
    { BaseE e }
  | LID e = expr3
    { LidE e }
  | CORE e = expr3
    { CoreE e }
  | CYL b = expr3 l = expr3 c = expr3
    { CylE (b,l,c) }
  | coh = coh_expr
    { coh } 
  | LPAR t = expr RPAR
    { t }

paren_pd:
  | LPAR brs = suite(paren_pd) RPAR
    { ((),Pd.Br ((),brs)) }

ucomp_pd:
  | pd = paren_pd
    { UnitPd (snd pd) }
  | ds = INT+
    { IntSeq ds }

pd_with_tgt:
  | pd = id_pd tgt = IDENT
    { (VarE tgt,pd) }

id_pd:
  | LPAR src = IDENT brs = suite(pd_with_tgt)
    { Pd.Br (VarE src,brs) }

pd_expr:
  | tl = tele
    { TelePd tl }
  | cat = IDENT pd = id_pd
    { TreePd (VarE cat,pd) }

sph_expr:
  |
    {Emp}
  | sph = sph_expr VBAR src = expr2 DBLARROW tgt = expr2
    { Ext (sph,(src,tgt)) }

disc_expr:
  | sph = sph_expr VBAR d = expr2
    { (sph,d) }

coh_expr:
  | COMP LBRKT pd = pd_expr COLON cat = expr BARARROW src = expr2 DBLARROW tgt = expr2 RBRKT
    { CompE (pd,cat,src,tgt) }
  | UCOMP LBRKT upd = ucomp_pd RBRKT
    { UCompE upd }
  | COH LBRKT pd = pd_expr COLON cat = expr BARARROW src = disc_expr IFF tgt = disc_expr RBRKT
    { CohE (pd,cat,src,tgt) }
