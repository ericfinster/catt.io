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
   | AppE of tm_expr * tm_expr
   | CellE of cell_expr

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
  | PiT of ty_term * ty_term 
          
 and tm_term =
   | BVarT of int
   | FVarT of string
   | CellT of cell_term
   | AppT of tm_term * tm_term

 and cell_term =
   | CohT of ty_term list * ty_term
   | CompT of ty_term list * ty_term   

type ctx = (string * ty_term) list

let rec print_ty_term t =
  match t with
  | ObjT -> "*"
  | ArrT (typ, src, tgt) -> 
     sprintf "%s | %s -> %s" (print_ty_term typ)
             (print_tm_term src) (print_tm_term tgt)
  | PiT (a, b) ->
     sprintf "Pi (%s) (%s)" (print_ty_term a) (print_ty_term b)

and print_tm_term t =
  match t with
  | BVarT k -> sprintf "%d" k 
  | FVarT id -> id
  | CellT cell -> print_cell_term cell
  | AppT (u , v) ->
     sprintf "%s %s" (print_tm_term u) (print_tm_term v)
             
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
            
(* Semantic domain for normalization *)
            
type dom_ty =
  | ObjD
  | ArrowD of dom_ty * dom_tm * dom_tm
  | PiD of dom_ty * (dom_tm -> dom_ty)

 and dom_tm =
   | VarD of int
   | AppD of dom_tm * dom_tm
         
