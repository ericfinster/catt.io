(*
 *  pd.ml - pasting diagram routines
 *)

open Common
open Term
  
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
          (fun _ -> Succeed args_done)

(* Last step is the initial argument *)  
let pd_zip_expand_args pd lm_args =
  zipper_open_right pd >>== fun z ->
  match lm_args with
  | [] -> Fail "No arguments"
  | (tm,ty)::_ ->
     nth_src tm ty (dim_of ty) >>== fun (init_arg,_) -> 
     pd_zip_consume_args z 0 lm_args (init_arg::[])
  
