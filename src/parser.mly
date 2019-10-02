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
  | DEF id = IDENT ctx = var_decl+ COLON ty = expr
    { Def (id, List.rev ctx, ty) }
  | LET id = IDENT ctx = var_decl+ COLON ty = expr EQUALS tm = expr
    { Let (id, List.rev ctx, ty, tm) }

var_decl:
  | LPAR id = IDENT COLON ty = expr RPAR
    { (id, ty) }

expr:
  | e = expr1
    { e } 
  | e1 = expr1 ARROW e2 = expr
    { ArrowE (e1, e2) } 

expr1:
  | e = expr2
    { e }
  | COH pd = var_decl+ COLON ty = expr1
    { CohE (pd, ty) }
  | COMP pd = var_decl+ COLON ty = expr1
    { CompE (pd, ty) }

expr2:
  | e = expr3
    { e }
  | e1 = expr2 e2 = expr3
    { AppE (e1 , e2) }

expr3:
  | OBJ
    { ObjE }
  | id = IDENT
    { VarE id }
  | LPAR e = expr RPAR
    { e }
