(*
 * common.ml - utility items
 *)

(* An error monad *)
type 'a err =
  | Fail of string
  | Succeed of 'a

(* Bind for the error monad *)
let ( >>== ) m f =
  match m with
  | Fail s -> Fail s
  | Succeed a -> f a
