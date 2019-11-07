(*
 * syntax.ml - syntactic definitions
 *)

open Printf

module SS = Set.Make(String)
          
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

(* Find the dimension of a type *)
let rec dim_of typ =
  match typ with
  | ObjT -> 0
  | ArrT (ty, _, _) -> 1 + (dim_of ty)

(* Free variables *)
let rec ty_free_vars t =
  match t with
  | ObjT -> SS.empty
  | ArrT (typ, src, tgt) ->
     let typ_fvs = ty_free_vars typ in
     let src_fvs = tm_free_vars src in
     let tgt_fvs = tm_free_vars tgt in
     List.fold_right SS.union [typ_fvs; src_fvs; tgt_fvs] SS.empty

and tm_free_vars t =
  match t with
  | VarT id -> SS.singleton id
  | DefAppT (_, args) ->
     List.fold_right SS.union (List.map tm_free_vars args) SS.empty
  | CellAppT (cell, args) -> 
     let args_fvs = List.fold_right SS.union (List.map tm_free_vars args) SS.empty in
     SS.union (cell_free_vars cell) args_fvs

and cell_free_vars t =
  match t with
  | CohT (_, typ) -> ty_free_vars typ
  | CompT (_, typ) -> ty_free_vars typ

(* Simultaneous Substitution *)

let rec subst_ty s t =
  match t with
  | ObjT -> ObjT
  | ArrT (typ, src, tgt) ->
     let typ' = subst_ty s typ in
     let src' = subst_tm s src in
     let tgt' = subst_tm s tgt in
     ArrT (typ', src', tgt')

and subst_tm s t =
  match t with
  | VarT id -> List.assoc id s
  | DefAppT (id, args) ->
     DefAppT (id, List.map (subst_tm s) args)
  | CellAppT (cell, args) ->
     CellAppT (subst_cell s cell, List.map (subst_tm s) args)

and subst_cell s t =
  match t with
  | CohT (pd, typ) -> CohT (pd, subst_ty s typ)
  | CompT (pd, typ) -> CompT (pd, subst_ty s typ)
    
(* Printing of types and terms *)                     
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


(* Contexts and Environments *)
    
type ctx = (string * ty_term) list
type env = (string * tm_term) list 
    
(* Semantic domain for normalization *)
            
type dom_ty =
  | ObjD
  | ArrowD of dom_ty * dom_tm * dom_tm
  | PiD of dom_ty * (dom_tm -> dom_ty)

 and dom_tm =
   | VarD of int
   | AppD of dom_tm * dom_tm
         
