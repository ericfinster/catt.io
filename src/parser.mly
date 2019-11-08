%{

  open Syntax
  
%} 

%token LET
%token COH COMP
%token OBJ ARROW 
%token LPAR RPAR LBRACKET RBRACKET
%token COMMA COLON EQUAL
%token <string> IDENT 
%token EOF

%start prog
%type <Syntax.cmd list> prog
%%

prog:
  | EOF
    { [] }
  | cmds = nonempty_list(cmd) EOF
    { cmds }

cmd:
  | LET id = IDENT EQUAL cell = cell_expr
    { CellDef (id, cell) }
  | LET id = IDENT ctx = var_decl+ COLON ty = ty_expr EQUAL tm = tm_expr
    { TermDef (id, List.rev ctx, ty, tm) }

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
    { CellAppE (cell, args) }
  | id = IDENT LPAR args = separated_nonempty_list(COMMA, tm_expr) RPAR
    { DefAppE (id, args) } 
  | id = IDENT
    { VarE id }
    
cell_expr:
  | COH pd = var_decl+ COLON ty = ty_expr
    { CohE (List.rev pd, ty) }
  | COMP pd = var_decl+ COLON ty = ty_expr
    { CompE (List.rev pd, ty) }
