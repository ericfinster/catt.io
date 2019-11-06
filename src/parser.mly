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
    { ObjTypE }
  | e1 = tm_expr ARROW e2 = tm_expr
    { ArrowTypE (e1, e2) }

tm_expr:
  | id = IDENT
    { VarTmE id }
  | coh = coh_expr
    { CohTmE coh }

coh_expr:
  | COH pd = var_decl+ COLON ty = ty_expr
    { CohE (pd, ty) }
  | COMP pd = var_decl+ COLON ty = ty_expr
    { CompE (pd, ty) }