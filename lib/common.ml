(*
 * common.ml - utility items
 *)

open List
open Cheshire.Err

open ErrMonad
  
(* Simple list zipper routines for manipulating pd's *)
type 'a zipper = 'a * ('a list) * ('a list)

let zipper_head (a, _, _) = a
let zipper_left_list (_,ls,_) = ls
let zipper_right_list (_,_,rs) = rs
                          
let zipper_open = function
  | [] -> Fail "Cannot open empty list"
  | l::ls -> Ok (l,[],ls)
  
let zipper_close = function
  | (a, ls, rs) -> (rev ls) @ (a::rs)
               
let zipper_move_left = function
  | (a, l::ls, rs) -> Ok (l, ls, a::rs)
  | _ -> Fail "Empty left list in move"

let zipper_move_right = function
  | (a, ls, r::rs) -> Ok (r, a::ls, rs)
  | _ -> Fail "Empty right list in move"
    
let zipper_drop_left = function
  | (_ , l :: ls, rs) -> Ok (l , ls, rs)
  | _ -> Fail "Empty left list"

let zipper_drop_right = function
  | (_, ls, r::rs) -> Ok (r, ls, rs)
  | _ -> Fail "Empry right list"

let rec zipper_scan_right f z =
  if (f (zipper_head z)) then
    Ok z
  else zipper_move_right z >>=
    zipper_scan_right f

let zipper_has_left = function
  | (_, [], _) -> false
  | _ -> true

let zipper_has_right = function
  | (_, _, []) -> false
  | _ -> true 

let rec zipper_rightmost z =
  if (zipper_has_right z) then
    zipper_move_right z >>=
    zipper_rightmost
  else Ok z 

let zipper_open_right l =
  zipper_open l >>=
  zipper_rightmost

