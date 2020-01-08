(*
 * common.ml - utility items
 *)

open List
   
(* An error monad *)
type 'a err =
  | Fail of string
  | Succeed of 'a

(* Bind for the error monad *)
let ( >>== ) m f =
  match m with
  | Fail s -> Fail s
  | Succeed a -> f a

(* A try-catch routine for err *)               
let err_try m case_ok case_fail =
  match m with
  | Fail s -> case_fail s
  | Succeed a -> case_ok a 
  
(* Simple list zipper routines for manipulating pd's *)
type 'a zipper = 'a * ('a list) * ('a list)

let zipper_head (a, _, _) = a
let zipper_left_list (_,ls,_) = ls
let zipper_right_list (_,_,rs) = rs
                          
let zipper_open = function
  | [] -> Fail "Cannot open empty list"
  | l::ls -> Succeed (l,[],ls)
  
let zipper_close = function
  | (a, ls, rs) -> (rev ls) @ (a::rs)
               
let zipper_move_left = function
  | (a, l::ls, rs) -> Succeed (l, ls, a::rs)
  | _ -> Fail "Empty left list in move"

let zipper_move_right = function
  | (a, ls, r::rs) -> Succeed (r, a::ls, rs)
  | _ -> Fail "Empty right list in move"
    
let zipper_drop_left = function
  | (_ , l :: ls, rs) -> Succeed (l , ls, rs)
  | _ -> Fail "Empty left list"

let zipper_drop_right = function
  | (_, ls, r::rs) -> Succeed (r, ls, rs)
  | _ -> Fail "Empry right list"

let rec zipper_scan_right f z =
  if (f (zipper_head z)) then Succeed z else
    zipper_move_right z >>== fun z' ->
    zipper_scan_right f z'

let zipper_has_left = function
  | (_, [], _) -> false
  | _ -> true

let zipper_has_right = function
  | (_, _, []) -> false
  | _ -> true 

let rec zipper_rightmost z =
  if (zipper_has_right z) then
    zipper_move_right z >>== fun zr ->
    zipper_rightmost zr
  else Succeed z 

let zipper_open_right l =
  zipper_open l >>==
    zipper_rightmost
  
