(*
 * term.ml - internal term representation
 *)

open Printf

module SS = Set.Make(String)
                    
(* Internal term representation *)
type ty_term =
  | ObjT
  | ArrT of ty_term * tm_term * tm_term
          
 and tm_term =
   | VarT of string
   | DefAppT of string * tm_term list
   | CellAppT of cell_term * tm_term list

 and cell_term =
   | CohT of ctx * ty_term
   | CompT of ctx * ty_term   

 and ctx = (string * ty_term) list
 and env = (string * tm_term) list 

(* The identity substitution of a context *)    
let id_args gma =
  List.map (fun (id, _) -> VarT id) gma

let id_sub gma =
  List.map (fun (id, _) -> (id, VarT id)) gma
  
(* Find the dimension of a type *)
let rec dim_of typ =
  match typ with
  | ObjT -> 0
  | ArrT (ty, _, _) -> 1 + (dim_of ty)

(* Dimension of a pasting diagram *)          
let dim_of_pd pd =
  List.fold_right max (List.map (fun (_, typ) -> dim_of typ) pd) 0

let cell_pd cell =
  match cell with
  | CohT (pd, _) -> pd
  | CompT (pd, _) -> pd

let cell_typ cell =
  match cell with
  | CohT (_, typ) -> typ
  | CompT (_, typ) -> typ

(* Return the identity coherence on the given cell *)
let cell_id cell =
  let pd = cell_pd cell in
  let ty = cell_typ cell in
  let tm = CellAppT (cell, id_args pd) in 
  CohT (pd, ArrT (ty, tm, tm))

(* Return the disc pasting diagram of a given dimension *)
let rec disc_pd_with_typ k =
  if (k <= 0) then (("ds0", ObjT) :: [], ObjT)
  else let tgt_id = sprintf "dt%d" (k-1) in
       let src_id = sprintf "ds%d" (k-1) in 
       let dsc_id = sprintf "ds%d" k in
       let (dpd, last_ty) = disc_pd_with_typ (k-1) in
       let next_ty = ArrT (last_ty, VarT src_id, VarT tgt_id) in
       ((dsc_id, next_ty) :: (tgt_id, last_ty) :: dpd, next_ty)
       
let disc_pd k = fst (disc_pd_with_typ k)

(* Return the canonical identity coherence in 
 * dimension k *)              
let id_coh k =
  let (dsc, sph) = disc_pd_with_typ k in
  let dsc_id = sprintf "ds%d" k in 
  CohT (dsc, ArrT (sph, VarT dsc_id, VarT dsc_id))

(* From a term and its type, return an appropriate
 * substitution to a disc *)  
let rec tm_to_disc_sub tm ty =
  match ty with
  | ObjT -> [tm]
  | ArrT (typ', src, tgt) ->
     let s = tm_to_disc_sub src typ' in
     tm :: tgt :: s
  
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

(* Printing of types and terms *)                     
let rec print_ty_term t =
  match t with
  | ObjT -> "*"
  | ArrT (_, src, tgt) -> 
     sprintf "%s -> %s" 
             (print_tm_term src) (print_tm_term tgt)
     (* sprintf "%s | %s -> %s" (print_ty_term typ) *)
     (*         (print_tm_term src) (print_tm_term tgt) *)
    
and print_tm_term t =
  let print_args args =
    String.concat ", " (List.map print_tm_term (List.rev args)) in 
  match t with
  | VarT id -> id
  | DefAppT (id, args) ->
     sprintf "%s(%s)" id (print_args args)
  | CellAppT (cell, args) -> 
     sprintf "[%s](%s)" (print_cell_term cell) (print_args args)
             
and print_cell_term t =
  let print_decl (id, typ) =
    sprintf "(%s : %s)" id (print_ty_term typ) in 
  let print_pd pd =
    String.concat " " (List.map print_decl (List.rev pd)) in 
  match t with
  | CohT (pd, typ) ->
     sprintf "coh %s : %s" (print_pd pd) (print_ty_term typ)
  | CompT (pd, typ) ->
     sprintf "comp %s : %s" (print_pd pd) (print_ty_term typ)
         
let print_term_ctx g =
  let print_decl = fun (id, typ) ->
    sprintf "(%s : %s)" id (print_ty_term typ) in 
  let decls = List.map print_decl g in
  String.concat " " (List.rev decls)
  
let print_sub s =
  let print_sub_entry = fun (id, tm) ->
    sprintf "%s -> %s" id (print_tm_term tm) in
  let entries = List.map print_sub_entry s in
  String.concat "; " (List.rev entries)
                    
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
  | VarT id -> (try List.assoc id s
                with Not_found ->
                     printf "Lookup failed for %s in substitution %s\n" id (print_sub s);
                     raise Not_found)
  | DefAppT (id, args) ->
     DefAppT (id, List.map (subst_tm s) args)
  | CellAppT (cell, args) ->
     CellAppT (subst_cell s cell, List.map (subst_tm s) args)

and subst_cell s t =
  match t with
  | CohT (pd, typ) -> CohT (pd, subst_ty s typ)
  | CompT (pd, typ) -> CompT (pd, subst_ty s typ)

(* Rename a variable in a type or term.
 * Warning! This routine could capture variables. 
 * Use with care. *)
(* let rec rename_ty sid tid t = *)
(*   match t with *)
(*   | ObjT -> ObjT *)
(*   | ArrT (typ, src, tgt) -> *)
(*      let typ' = rename_ty sid tid typ in *)
(*      let src' = rename_tm sid tid src in *)
(*      let tgt' = rename_tm sid tid tgt in *)
(*      ArrT (typ', src', tgt') *)

(* and rename_tm sid tid t = *)
(*   match t with *)
(*   | VarT id -> if (id = sid) then VarT tid else VarT id *)
(*   | DefAppT (id, args) -> *)
(*      DefAppT (id, List.map (rename_tm sid tid) args) *)
(*   | CellAppT (cell, args) -> *)
(*      CellAppT (rename_cell sid tid cell, List.map (rename_tm sid tid) args) *)

(* and rename_cell sid tid t = *)
(*   match t with *)
(*   | CohT (pd, typ) -> CohT (pd, rename_ty sid tid typ) *)
(*   | CompT (pd, typ) -> CompT (pd, rename_ty sid tid typ) *)
                     
