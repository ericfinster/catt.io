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
                                
let pd_zip_is_loc_max z =
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
       (* Rename the target variable to the source
        * variable in the left list. *)
       let a = zipper_head zrr in
       let ls = List.map (fun ((id,ty),tm) -> ((id,rename_ty tgt_id src_id ty),tm))
                         (zipper_left_list zrr) in
       let rs = zipper_right_list zrr in 
       Succeed (a, ls, rs)
    | ArrT (_, _, _) -> Fail "Malformed pasting diagram"

  
