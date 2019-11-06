(*
 * syntax.ml - syntactic definitions
 *)

(* Slightly refined user expressions *)
          
type ty_expr =
  | ObjTypE
  | ArrowTypE of tm_expr * tm_expr

 and tm_expr =
   | VarTmE of string
   | AppTmE of tm_expr * tm_expr
   | CohTmE of coh_expr

 and coh_expr =
   | CohE of (string * ty_expr) list * ty_expr
   | CompE of (string * ty_expr) list * ty_expr
     
(* Commands *)
type cmd =
  | Def of string * (string * ty_expr) list * ty_expr
  | Let of string * (string * ty_expr) list * ty_expr * tm_expr

(* Internal, locally nameless representation *)
         
type ty_term =
  | ObjT
  | ArrowT of ty_term * tm_term * tm_term

 and tm_term =
   | CattT of catt_term
   | AppT of tm_term * tm_term
   | BVarT of int
   | FVarT of string

 and catt_term =
   | CohT of ty_term list * ty_term
   | CompT of ty_term list * ty_term   
   
            
(* Semantic domain for normalization *)
            
type dom_ty =
  | ObjD
  | ArrowD of dom_ty * dom_tm * dom_tm
  | PiD of dom_ty * (dom_tm -> dom_ty)

 and dom_tm =
   | VarD of int
   | AppD of dom_tm * dom_tm
         
