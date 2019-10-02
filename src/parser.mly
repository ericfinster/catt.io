%{

  open Typecheck
  
%} 

%token COH OBJ ARROW PIPE
%token LPAR RPAR COLON
%token <string> IDENT 
%token EOF

%start prog
%type <Typecheck.decl list> prog
%%

prog:
  | EOF
    { [] }
  | decls = nonempty_list(decl) EOF
    { decls }

decl:
  | COH id = IDENT ctx = nonempty_list(var_decl) COLON ty = typ 
    { Coh (id, ctx, ty) }

typ:
  | OBJ
    { Star }
  | t = typ PIPE src = trm ARROW tgt = trm
    { Arrow (t, src, tgt) }

trm:
  | id = IDENT
    { Var id }
    
var_decl:
  | LPAR id = IDENT COLON ty = typ RPAR
    { (id, ty) }
