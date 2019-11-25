(*
 *  pd.ml - pasting diagram routines
 *)

open Common
open Term
  
type pd_and_args = (string * ty_term) * tm_term
type pd_zip = pd_and_args zipper 

let pd_zip_head_ty (((_,ty),_),_,_) = ty
let pd_zip_head_tm (((_,_),tm),_,_) = tm
let pd_zip_head_id (((id,_),_),_,_) = id

let pd_zip_with_head_ty ty (((id,_),tm),ls,rs) = (((id,ty),tm),ls,rs)
                                    
let pd_zip_is_loc_max z =
  (* Printf.printf "Checking if cell %s is locally maximal\n" (pd_zip_head_id z); *)
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

(* Starting from a substitution, accumulate
 * any remaing variables as identities while
 * applying the accumulated substitution to 
 * the types in the pasting diagram *)
let rec pd_zip_extend_sub z s =
  err_try (zipper_move_left z)
          (fun zl ->
            let id = pd_zip_head_id zl in
            let ty = subst_ty s (pd_zip_head_ty zl) in
            pd_zip_extend_sub (pd_zip_with_head_ty ty zl)
                              ((id,VarT id)::s))
          (fun _ -> Succeed (z,s))
  
  
(* Drop a locally maximal cell and its target, together
 * with their arguments. *)
let pd_zip_drop z =
  pd_zip_is_loc_max z >>== fun is_lmax ->
  if (not is_lmax) then
    Fail "Cannot drop non-locally maximal cell"
  else
    match pd_zip_head_ty z with
    | ObjT -> Fail "Cannot drop and object"
    | ArrT (_, VarT src_id, VarT tgt_id) ->
       zipper_drop_right z >>== fun zr ->
       zipper_drop_right zr >>== fun zrr ->
       let r_id = pd_zip_head_id zrr in 
       let s = (tgt_id,VarT src_id)::(r_id,VarT r_id)::(id_sub (fst (List.split (zipper_right_list zrr)))) in
       pd_zip_extend_sub zrr s >>== fun (z', s') ->
       zipper_scan_right (fun ((id,_),_) -> id = r_id) z' >>== fun zr ->
       Succeed (zr, s')
    | ArrT (_, _, _) -> Fail "Malformed pasting diagram"

  
