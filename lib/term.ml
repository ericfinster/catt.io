(*
 * term.ml - internal term representation
 *)

open Common
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

(* Return the opposite of a type *)
let opposite typ =
  match typ with
  | ObjT -> ObjT
  | ArrT (typ,src,tgt) ->
     ArrT (typ,tgt,src)

(* Return the identity coherence on the given cell *)
let cell_id cell =
  let pd = cell_pd cell in
  let ty = cell_typ cell in
  let tm = CellAppT (cell, id_args pd) in
  CohT (pd, ArrT (ty, tm, tm))

(* Return the disc pasting diagram of a given dimension *)
let rec disc_pd_with_typ k =
  if (k <= 0) then (("x0", ObjT) :: [], ObjT)
  else let tgt_id = sprintf "x%d" (2 * (k-1) + 1) in
       let src_id = sprintf "x%d" (2 * (k-1)) in
       let dsc_id = sprintf "x%d" (2 * k) in
       let (dpd, last_ty) = disc_pd_with_typ (k-1) in
       let next_ty = ArrT (last_ty, VarT src_id, VarT tgt_id) in
       ((dsc_id, next_ty) :: (tgt_id, last_ty) :: dpd, next_ty)

let disc_pd k = fst (disc_pd_with_typ k)

(* Source and target functions *)
let rec nth_src tm ty n =
  if (n <= 0) then Succeed (tm, ty)
  else match ty with
       | ObjT -> Fail "Object has no source"
       | ArrT (typ,src,_) -> nth_src src typ (n-1)

let rec nth_tgt tm ty n =
  if (n <= 0) then Succeed (tm, ty)
  else match ty with
       | ObjT -> Fail "Object has no source"
       | ArrT (typ,_,tgt) -> nth_tgt tgt typ (n-1)

(* Append a disc of dimension n to this pasting
 * diagram starting in codimension k. Use idx as
 * a count for variable names.
 *)
let rec append_disc k n pd idx =
  match pd with
  | [] -> Fail "Empty pasting diagram"
  | (f_id, f_typ)::_ ->
     nth_tgt (VarT f_id) f_typ k >>== fun (src_tm, typ)->
     let d = dim_of typ in
     if (n < d) then
       Fail "Disc dimension too low"
     else if (n = d) then
       Succeed pd
     else
       let tgt_id = sprintf "x%d" idx in
       let dsc_id = sprintf "x%d" (idx+1) in
       let pd' = (dsc_id, ArrT (typ,src_tm,VarT tgt_id))::(tgt_id, typ)::pd in
       append_disc 0 n pd' (idx+2)

(* Build a pasting diagram consisting of a single
 * n-cell and two k-cells glued to its source and
 * target k-1 boundary. (k >= 1)
 *)
let pad_pd k n =
  let k_dsc = disc_pd k in
  append_disc 1 n k_dsc (2*k + 1) >>== fun pd ->
  append_disc (n-k+1) k pd (List.length pd)

(* Return the canonical identity coherence in
 * dimension k *)
let id_coh k =
  let (dsc, sph) = disc_pd_with_typ k in
  let dsc_id = sprintf "x%d" (2 * k) in
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
  | CellAppT (_, args) ->
     List.fold_right SS.union (List.map tm_free_vars args) SS.empty

and cell_free_vars t =
  match t with
  | CohT (_, typ) -> ty_free_vars typ
  | CompT (_, typ) -> ty_free_vars typ


(*
 * Simultaneous Substitution
 *)

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
                (*           (try List.assoc id s *)
                (* with Not_found -> *)
                (*      printf "Lookup failed for %s in substitution %s\n" id (print_sub s); *)
                (*      raise Not_found) *)
  | DefAppT (id, args) ->
     DefAppT (id, List.map (subst_tm s) args)
  | CellAppT (cell, args) ->
     (* Does one every have free variables inside a cell declaration? *)
     CellAppT (cell, List.map (subst_tm s) args)
     (* CellAppT (subst_cell s cell, List.map (subst_tm s) args) *)

and subst_cell s t =
  match t with
  | CohT (pd, typ) -> CohT (pd, subst_ty s typ)
  | CompT (pd, typ) -> CompT (pd, subst_ty s typ)


(*
 * Zippers for pasting diagrams
 *)

type pd_and_args = (string * ty_term) * tm_term
type app_zip = pd_and_args zipper

let app_zip_head_ty (((_,ty),_),_,_) = ty
let app_zip_head_tm (((_,_),tm),_,_) = tm
let app_zip_head_id (((id,_),_),_,_) = id

let app_zip_with_head_ty ty (((id,_),tm),ls,rs) = (((id,ty),tm),ls,rs)

let app_zip_is_loc_max z =
  (* Printf.printf "Checking if cell %s is locally maximal\n" (app_zip_head_id z); *)
  err_try (zipper_move_left z)
          (fun zl -> let head_ty = app_zip_head_ty z in
                     let left_ty = app_zip_head_ty zl in
                     Succeed ((dim_of left_ty) < (dim_of head_ty)))
          (fun _ -> Succeed true)

let rec app_zip_next_loc_max z =
  err_try (zipper_move_left z)
          (fun zl -> app_zip_is_loc_max zl >>== fun is_lmax ->
                     if (is_lmax) then Succeed zl
                     else app_zip_next_loc_max zl)
          (fun _ -> Fail "No more locally maximal cells")

(* Starting from a substitution, accumulate
 * any remaing variables as identities while
 * applying the accumulated substitution to
 * the types in the pasting diagram *)
let rec app_zip_extend_sub z s =
  err_try (zipper_move_left z)
          (fun zl ->
            let id = app_zip_head_id zl in
            let ty = subst_ty s (app_zip_head_ty zl) in
            app_zip_extend_sub (app_zip_with_head_ty ty zl)
                              ((id,VarT id)::s))
          (fun _ -> Succeed (z,s))

(* Extract the remaining locally maximal arguments
 * from the provided zipper
 *)
let rec app_zip_extract_remaining_loc_max z lms =
  err_try (app_zip_next_loc_max z)
          (fun zlm -> let lm_arg = app_zip_head_tm zlm in
                      app_zip_extract_remaining_loc_max zlm (lm_arg::lms))
          (fun _ -> Succeed lms)

(* Drop a locally maximal cell and its target, together
 * with their arguments. Return a substitution which
 * inserts an identity in the appropriate place. *)
let app_zip_drop z =
  app_zip_is_loc_max z >>== fun is_lmax ->
  if (not is_lmax) then
    Fail "Cannot drop non-locally maximal cell"
  else
    match app_zip_head_ty z with
    | ObjT -> Fail "Cannot drop and object"
    | ArrT (bdry_typ, VarT src_id, VarT tgt_id) ->
       zipper_drop_right z >>== fun zr ->
       zipper_drop_right zr >>== fun zrr ->
       let fill_id = app_zip_head_id z in
       let id_tm = CellAppT (id_coh (dim_of bdry_typ), tm_to_disc_sub (VarT src_id) bdry_typ) in
       let s = (fill_id, id_tm)::
                 (tgt_id,VarT src_id)::
                   (src_id,VarT src_id)::
                     (id_sub (fst (List.split (zipper_right_list zrr)))) in
       app_zip_extend_sub zrr s >>== fun (z', s') ->
       zipper_scan_right (fun ((id,_),_) -> id = src_id) z' >>== fun zr ->
       Succeed (zr, s')
    | ArrT (_, _, _) -> Fail "Malformed pasting diagram"


(*
 *  A zipper for pasting diagrams w/o arguments
 *)

type pd_zip = (string * ty_term) zipper

let pd_zip_head_ty ((_,ty),_,_) = ty
let pd_zip_head_id ((id,_),_,_) = id

let pd_zip_is_loc_max z =
  (* Printf.printf "Checking if cell %s is locally maximal\n" (app_zip_head_id z); *)
  err_try (zipper_move_left z)
          (fun zl -> let head_ty = pd_zip_head_ty z in
                     let left_ty = pd_zip_head_ty zl in
                     Succeed ((dim_of left_ty) < (dim_of head_ty)))
          (fun _ -> Succeed true)

let rec pd_zip_next_loc_max z =
  err_try (zipper_move_left z)
          (fun zl -> pd_zip_is_loc_max zl >>== fun is_lmax ->
                     if (is_lmax) then Succeed zl
                     else pd_zip_next_loc_max zl)
          (fun _ -> Fail "No more locally maximal cells")

let rec take n l =
  match l with
  | [] -> []
  | x::xs -> if (n = 0) then []
             else x::(take (n-1) xs)

let rec pd_zip_consume_args z k args_rem args_done =
  err_try (pd_zip_next_loc_max z)
          (fun zlm -> match args_rem with
                      | [] -> Fail "Ran out of arguments"
                      | (tm,ty)::args_rem' ->
                         let n = dim_of (pd_zip_head_ty zlm) in
                         let codim = n - k in
                         let new_args = take (2 * codim) (tm_to_disc_sub tm ty) in
                         let args_done' = new_args @ args_done in
                         let k' = (match zipper_left_list zlm with
                                   | [] -> 0
                                   | (_,nxt_typ)::_ -> dim_of nxt_typ) in
                         pd_zip_consume_args zlm k' args_rem' args_done'
          )
          (fun _ -> if (List.length args_rem > 0) then
                      Fail "Too many arguments"
                    else Succeed args_done)

(* Last step is the initial argument *)
let pd_zip_expand_args pd lm_args =
  (* let print_pair = fun (tm, ty) -> *)
  (*   sprintf "(%s : %s)" (print_tm_term tm) (print_ty_term  ty) in *)
  (* printf "Expanding locally maximal arguments: \n%s\n" (String.concat "\n" (List.map print_pair lm_args)); *)
  zipper_open_right pd >>== fun z ->
  let lm_args_rev = List.rev lm_args in
  match lm_args_rev with
  | [] -> Fail "No arguments"
  | (tm,ty)::_ ->
     nth_src tm ty (dim_of ty) >>== fun (init_arg,_) ->
     let init_args_done = (init_arg::[]) in
     if (List.length pd = 1) then
       (* We have to single out the trivial pasting diagram so that
        * the excess argument detection above does not give false
        * positives in this case .... *)
       Succeed init_args_done
     else pd_zip_consume_args z 0 lm_args_rev (init_arg::[]) >>== fun result ->
     (* printf "Results: \n%s\n" (String.concat "\n" (List.map print_tm_term result)); *)
     Succeed result


(*
 * Printing of types and terms
 *)

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
     (* sprintf "[%s](%s)" (print_cell_term cell) (print_args args) *)
     let pd = cell_pd cell in
     if (List.length pd = 1) then
       sprintf "[%s](%s)" (print_cell_term cell) (print_args args)
     else
       let pd_and_args = List.combine pd args in
       let m = zipper_open_right pd_and_args >>== fun z ->
               app_zip_extract_remaining_loc_max z [] in
       match m with
       | Fail msg -> sprintf "**** %s ****" msg
       | Succeed lm_args -> sprintf "[%s](%s)" (print_cell_term cell) (print_args lm_args)

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

let print_args args =
  String.concat ", " (List.map print_tm_term args)


(* A binary predicate which decides if a given
 * context is in fact a disc pasting diagram and
 * returns the top dimensional variable as well
 * as its type.
 *)
let rec is_disc_pd pd =
  match pd with
  | [] -> Fail "Empty context"
  | (id, ObjT) :: [] -> Succeed (id, ObjT)
  | (_, _) :: [] -> Fail "Not a pasting diagram"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     is_disc_pd pd' >>== fun (src_id, src_typ) ->
     if (tgt_typ <> src_typ) then
       Fail "Incorrect target type"
     else if (fill_typ <> ArrT (src_typ, VarT src_id, VarT tgt_id)) then
       Fail "Incorrect filler type"
     else Succeed (fill_id, fill_typ)

(* Is the given cell an identity coherence? Assumes the
 * term is already in normal form.  Returns the identifier
 * of the top dimensional variable and its type.
 *)
let is_identity_coh cell =
  match cell with
  | CohT (pd, ArrT (_, src, tgt)) ->
     is_disc_pd pd >>== fun (dsc_id, dsc_typ) ->
     if (src <> VarT dsc_id) then
       Fail "Wrong source"
     else if (tgt <> VarT dsc_id) then
       Fail "Wrong target"
     else Succeed (dsc_id, dsc_typ)
  | _ -> Fail "Not an identity"

(* Is the given cell an endomorphism coherence. Assumes
 * already in normal form.  Returns the source/target
 * term as well as its type.
 *)
let is_endomorphism_coh cell =
  match cell with
  | CohT (pd, ArrT (typ, src, tgt)) ->
     if (src = tgt) then
       Succeed (pd, src, typ)
     else Fail "Not an endomorphism"
  | _ -> Fail "Not an endo-coherence"

(* Is the given cell a unary composite? Assumes the
 * term is in normal form and returns the top dimensional
 * identifier and its type.
 *)
let is_unary_comp cell =
  match cell with
  | CompT (pd, typ) ->
     is_disc_pd pd >>== fun (dsc_id, dsc_typ) ->
     if (typ = dsc_typ) then
       Succeed (dsc_id, dsc_typ)
     else Fail "Wrong return type"
  | _ -> Fail "Not a unary comp"
