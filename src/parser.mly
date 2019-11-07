%{

  open Syntax
  
%} 

%token DEF LET
%token COH COMP
%token OBJ ARROW 
%token LPAR RPAR
%token COLON EQUALS
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
  | DEF id = IDENT ctx = var_decl+ COLON ty = ty_expr
    { Def (id, List.rev ctx, ty) }
  | LET id = IDENT ctx = var_decl+ COLON ty = ty_expr EQUALS tm = tm_expr
    { Let (id, List.rev ctx, ty, tm) }

var_decl:
  | LPAR id = IDENT COLON ty = ty_expr RPAR
    { (id, ty) }

ty_expr:
  | OBJ
    { ObjE }
  | e1 = tm_expr1 ARROW e2 = tm_expr
    { ArrE (e1, e2) }

tm_expr:
  | t = tm_expr1
    { t }
  | cell = cell_expr
    { CellE cell }
  
tm_expr1:
  | t = tm_expr2
    { t } 
  | t1 = tm_expr1 t2 = tm_expr2
    { AppE (t1, t2) }

tm_expr2:
  | id = IDENT
    { VarE id }
  | LPAR t = tm_expr RPAR
    { t }
    
cell_expr:
  | COH pd = var_decl+ COLON ty = ty_expr
    { CohE (pd, ty) }
  | COMP pd = var_decl+ COLON ty = ty_expr
    { CompE (pd, ty) }
