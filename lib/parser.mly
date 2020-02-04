%{

  open Expr
  
%} 

%token IMPORT
%token PRUNE RECTIFY NORMALIZE
%token EQNF LOCMAX
%token LET COH COMP
%token OBJ ARROW 
%token LPAR RPAR LBRACKET RBRACKET
%token COMMA COLON EQUAL VBAR
%token <string> IDENT 
%token EOF

%start prog
%type <string list * Expr.cmd list> prog

%start raw_cell
%type <Expr.cell_expr> raw_cell

%%

prog:
  | EOF
    { ([],[]) }
  | imprts = import* cmds = nonempty_list(cmd) EOF
    { (imprts, cmds) }

raw_cell:
  | ce = cell_expr EOF
    { ce }
  
import:
  | IMPORT id = IDENT
    { id }
    
cmd:
  | LET id = IDENT EQUAL cell = cell_expr
    { CellDef (id, cell) }
  | LET id = IDENT ctx = var_decl+ COLON ty = ty_expr EQUAL tm = tm_expr
    { TermDef (id, List.rev ctx, ty, tm) }
  | EQNF ctx = var_decl+ VBAR tm_a = tm_expr VBAR tm_b = tm_expr
    { EqNf (List.rev ctx, tm_a, tm_b) }
  | PRUNE ctx = var_decl+ VBAR tm = tm_expr
    { Prune (List.rev ctx, tm) }
  | RECTIFY ctx = var_decl+ VBAR tm = tm_expr
    { Rectify (List.rev ctx, tm) }
  | NORMALIZE ctx = var_decl+ VBAR tm = tm_expr
    { Normalize (List.rev ctx, tm) }
  | LOCMAX ctx = var_decl+
    { LocMax (List.rev ctx) }

var_decl:
  | LPAR id = IDENT COLON ty = ty_expr RPAR
    { (id, ty) }

ty_expr:
  | OBJ
    { ObjE }
  | e1 = tm_expr ARROW e2 = tm_expr
    { ArrE (e1, e2) }

tm_expr:
  | LBRACKET cell = cell_expr RBRACKET LPAR args = separated_nonempty_list(COMMA, tm_expr) RPAR
    { CellAppE (cell, List.rev args) }
  | id = IDENT LPAR args = separated_nonempty_list(COMMA, tm_expr) RPAR
    { DefAppE (id, List.rev args) } 
  | id = IDENT
    { VarE id }
    
cell_expr:
  | COH pd = var_decl+ COLON ty = ty_expr
    { CohE (List.rev pd, ty) }
  | COMP pd = var_decl+ COLON ty = ty_expr
    { CompE (List.rev pd, ty) }
