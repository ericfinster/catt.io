(*
 * syntax.ml - syntactic definitions
 *)

open Printf
   
(* Raw, user-level expressions *)
          
type ty_expr =
  | ObjE
  | ArrE of tm_expr * tm_expr

 and tm_expr =
   | VarE of string
   | DefAppE of string * tm_expr list
   | CellAppE of cell_expr * tm_expr list

 and cell_expr =
   | CohE of (string * ty_expr) list * ty_expr
   | CompE of (string * ty_expr) list * ty_expr
     
(* Commands *)
            
type cmd =
  | Def of string * (string * ty_expr) list * ty_expr
  | Let of string * (string * ty_expr) list * ty_expr * tm_expr

(* Internal, locally nameless representation *)
         
type ty_term =
  | ObjT
  | ArrT of ty_term * tm_term * tm_term
          
 and tm_term =
   | VarT of string
   | DefAppT of string * tm_term list
   | CellAppT of cell_term * tm_term list

 and cell_term =
   | CohT of ty_term list * ty_term
   | CompT of ty_term list * ty_term   

let rec print_ty_term t =
  match t with
  | ObjT -> "*"
  | ArrT (typ, src, tgt) -> 
     sprintf "%s | %s -> %s" (print_ty_term typ)
             (print_tm_term src) (print_tm_term tgt)
    
and print_tm_term t =
  let print_args args =
    String.concat ", " (List.map print_tm_term args) in 
  match t with
  | VarT id -> id
  | DefAppT (id, args) ->
     sprintf "%s(%s)" id (print_args args)
  | CellAppT (cell, args) -> 
     sprintf "[%s](%s)" (print_cell_term cell) (print_args args)
             
and print_cell_term t =
  let print_decl typ =
    sprintf "(%s)" (print_ty_term typ) in 
  let print_pd pd =
    String.concat " " (List.map print_decl pd) in 
  match t with
  | CohT (pd, typ) ->
     sprintf "coh %s : %s" (print_pd pd) (print_ty_term typ)
  | CompT (pd, typ) ->
     sprintf "comp %s : %s" (print_pd pd) (print_ty_term typ)


(* Contexts *)
    
type ctx = (string * ty_term) list

    
(* Semantic domain for normalization *)
            
type dom_ty =
  | ObjD
  | ArrowD of dom_ty * dom_tm * dom_tm
  | PiD of dom_ty * (dom_tm -> dom_ty)

 and dom_tm =
   | VarD of int
   | AppD of dom_tm * dom_tm
         
