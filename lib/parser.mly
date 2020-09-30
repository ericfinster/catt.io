%{

    open Expr
    open Suite
    open Command
     
%} 

%token IMPORT
%token PRUNE NORMALIZE INFER
%token SECTION WHERE END
%token LET COH 
%token OBJ ARROW 
%token LPAR RPAR LBRACKET RBRACKET
%token COMMA COLON EQUAL VBAR
%token <string> IDENT 
%token EOF

%start prog
%type <string list * Command.cmd list> prog

%%

prog:
  | EOF
    { ([],[]) }
  | imprts = import* cmds = nonempty_list(cmd) EOF
    { (imprts, cmds) }
  
import:
  | IMPORT id = IDENT
    { id }

decl:
  | LET id = IDENT tl = tele COLON ty = ty_expr EQUAL tm = tm_expr
    { (id, tl, ty, tm) }

cmd:
  | COH id = IDENT tl = tele COLON ty = ty_expr
    { CellDef (id, tl, ty) }
  | LET id = IDENT tl = tele COLON ty = ty_expr EQUAL tm = tm_expr
    { TermDef (id, tl, ty, tm) }
  | SECTION tl = tele WHERE decls = list(decl) END
    { Section (tl, decls) } 
  | PRUNE tl = tele VBAR tm = tm_expr
    { Prune (tl, tm) }
  | NORMALIZE tl = tele VBAR tm = tm_expr
    { Normalize (tl, tm) }
  | INFER tl = tele VBAR tm = tm_expr
    { Infer (tl, tm) }

tele:
  | v = var_decl
    { Ext (Emp, v) }
  | t = tele v = var_decl
    { Ext (t, v) }

var_decl:
  | LPAR id = IDENT COLON ty = ty_expr RPAR
    { (id, ty) }

ty_expr:
  | OBJ
    { ObjE }
  | e1 = tm_expr ARROW e2 = tm_expr
    { ArrE (e1, e2) }

arg_list:
  | tm = tm_expr
    { Ext (Emp, tm) }
  | tms = arg_list COMMA tm = tm_expr
    { Ext (tms, tm) }

tm_expr:
  | COH LBRACKET tl = tele COLON ty = ty_expr RBRACKET LPAR args = arg_list RPAR
    { CohE (tl,ty,args) }
  | id = IDENT LPAR args = arg_list RPAR
    { DefAppE (id, args) }
  | id = IDENT
    { VarE id }

