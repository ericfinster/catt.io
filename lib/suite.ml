(*****************************************************************************)
(*                                                                           *)
(*                            Suites (snoc lists)                            *)
(*                                                                           *)
(*****************************************************************************)

open Base

(*****************************************************************************)
(*                                    TODO                                   *)
(*                                                                           *)
(* 1. Write a container wrapper to be compatible with base                   *)
(* 2. Get rid of the exceptions for error types                              *)
(*                                                                           *)
(*****************************************************************************)

type 'a suite =
  | Emp
  | Ext of 'a suite * 'a

let (|>) a b = Ext (a, b)

let is_empty s =
  match s with
  | Emp -> true
  | _ -> false

let head s =
  match s with
  | Ext(_,a) -> a
  | _ -> failwith "head on empty"

let init s =
  match s with
  | Ext(s',_) -> s'
  | _ -> failwith "init on empty"

let rec match_init s =
  match s with
  | Emp -> failwith "match init on empty"
  | Ext (Emp,x) -> (x,Emp)
  | Ext (s',x) ->
    let (i,s'') = match_init s' in
    (i,Ext (s'',x))

let rec length s =
  match s with
  | Emp -> 0
  | Ext (s',_) -> length s' + 1

let rec map_suite s ~f =
  match s with
  | Emp -> Emp
  | Ext (s',x) -> map_suite s' ~f |> f x

let map_with_lvl s ~f =
  let rec go s =
    match s with
    | Emp -> (Emp , 0)
    | Ext (s',x) ->
      let (r,l) = go s' in
      (Ext (r,f l x),l+1)
  in fst (go s)

let rec filter s f =
  match s with
  | Emp -> Emp
  | Ext (s',x) ->
    let s'' = filter s' f in
    if (f x) then
      Ext (s'',x)
    else s''

let rec fold_left s a f =
  match s with
  | Emp -> a
  | Ext (s',x) -> f (fold_left s' a f) x

let rec fold_right s a f =
  match s with
  | Emp -> a
  | Ext (s',x) -> fold_right s' (f x a) f

let rec fold_accum_cont : 'a suite -> 'c -> ('a -> 'c -> 'b * 'c) -> ('b suite -> 'c -> 'd) -> 'd =
  fun s c f cont ->
  match s with
  | Emp -> cont Emp c
  | Ext (s',a) ->
    fold_accum_cont s' c f (fun s'' c' ->
        let (b,c'') = f a c' in
        cont (Ext (s'',b)) c'')

let rec fold2 s t init f =
  match (s,t) with
  | (Emp,Emp) -> init
  | (Ext (s',x), Ext (t',y)) ->
    f (fold2 s' t' init f) x y
  | _ -> failwith "unequal length suites"

let rec append s t =
  match t with
  | Emp -> s
  | Ext (t',x) -> Ext (append s t',x)

let (|*>) = append

let rec join ss =
  match ss with
  | Emp -> Emp
  | Ext (ss',s) -> append (join ss') s

let rec zip s t =
  match (s,t) with
  | (Emp,_) -> Emp
  | (_,Emp) -> Emp
  | (Ext (s',a), Ext (t',b)) ->
    Ext (zip s' t', (a, b))

let rec unzip s =
  match s with
  | Emp -> (Emp,Emp)
  | Ext (s',(a,b)) ->
    let (l,r) = unzip s' in
    (Ext (l,a), Ext (r,b))

let rec unzip3 s =
  match s with
  | Emp -> (Emp,Emp,Emp)
  | Ext (s',(a,b,c)) ->
    let (l,m,r) = unzip3 s' in
    (Ext (l,a), Ext (m,b), Ext (r,c))

let to_list s =
  let rec go s l =
    match s with
    | Emp -> l
    | Ext (s',x) -> go s' (x::l)
  in go s []

let zip_with_idx s =
  let rec zip_with_idx_pr s =
    match s with
    | Emp -> (Emp,0)
    | Ext (s',x) ->
      let (s'', i) = zip_with_idx_pr s' in
      (Ext (s'',(i,x)), i+1)
  in fst (zip_with_idx_pr s)

let rec range i j =
  if (i > j) then Emp
  else Ext (range i (j-1), j)

let rec repeat n x =
  if (n = 0) then
    Emp
  else Ext (repeat (n-1) x , x)

exception Lookup_error

let rec first s =
  match s with
  | Emp -> raise Lookup_error
  | Ext (Emp,x) -> x
  | Ext (s',_) -> first s'

let last s =
  match s with
  | Emp -> raise Lookup_error
  | Ext (_,x) -> x

let rec assoc k s =
  match s with
  | Emp -> raise Lookup_error
  | Ext (s',(k',v)) ->
    if (Poly.(=) k k') then v
    else assoc k s'

let assoc_with_idx k s =
  let rec go i k s =
    match s with
    | Emp -> raise Lookup_error
    | Ext (s',(k',v)) ->
      if (Poly.(=) k k') then (i,v)
      else go (i+1) k s'
  in go 0 k s

let singleton a = Ext (Emp, a)

let rec append_list s l =
  match l with
  | [] -> s
  | x::xs -> append_list (Ext (s,x)) xs

let from_list l =
  append_list Emp l

(* Extract de Brujin index from a suite *)
let rec db_get i s =
  match s with
  | Emp -> raise Lookup_error
  | Ext (s',x) ->
    if (i <= 0) then x
    else db_get (i-1) s'

(* Is there a version which doesn't traverse
   twice? *)
let nth n s =
  let l = length s in
  db_get (l-n-1) s

let rec grab k s =
  if (k<=0) then (s,[]) else
  let (s',r) = grab (k-1) s in
  match s' with
  | Emp -> raise Lookup_error
  | Ext (s'',x) -> (s'',x::r)

let split_at k s =
  let d = length s in
  grab (d-k) s

let rev s =
  let rec go s acc =
    match s with
    | Emp -> acc
    | Ext (s',x) -> go s' (Ext (acc,x))
  in go s Emp

(*****************************************************************************)
(*                                   Zipper                                  *)
(*****************************************************************************)

type 'a suite_zip = ('a suite * 'a * 'a list)

let close (l,a,r) =
  append_list (Ext(l,a)) r

let open_rightmost s =
  match s with
  | Emp -> Error "Empty suite on open"
  | Ext (s',a) -> Ok (s',a,[])

let move_left (l,a,r) =
  match l with
  | Emp -> Error "No left element"
  | Ext (l',a') -> Ok (l',a',a::r)

let move_right (l,a,r) =
  match r with
  | [] ->  Error "No right element"
  | a'::r' -> Ok (Ext (l,a),a',r')

let rec move_left_n n z =
  let open Base.Result.Monad_infix in
  if (n<=0) then Ok z else
    move_left z >>= move_left_n (n-1)

let open_leftmost s =
  let open Base.Result.Monad_infix in
  let n = length s in
  open_rightmost s >>= move_left_n (n-1)

let open_at k s =
  let open Base.Result.Monad_infix in
  let l = length s in
  if (k+1>l) then
    Error "Out of range"
  else open_rightmost s >>= move_left_n (l-k-1)

(*****************************************************************************)
(*                               Instances                                   *)
(*****************************************************************************)

module SuiteMnd = Monad.Make (struct
    type 'a t = 'a suite

    let return = singleton

    let map = `Custom map_suite

    let rec bind s ~f =
      match s with
      | Emp -> Emp
      | Ext (s',x) -> append (bind s' ~f) (f x)

  end)

(* include struct
 *   (\* We are explicit about what we import from the general Monad functor so that we don't
 *      accidentally rebind more efficient list-specific functions. *\)
 *   module Monad = Monad.Make (struct
 *       type 'a t = 'a list
 *
 *       let bind x ~f = concat_map x ~f
 *       let map = `Custom map
 *       let return x = [ x ]
 *     end)
 *
 *   open Monad
 *   module Monad_infix = Monad_infix
 *   module Let_syntax = Let_syntax
 *
 *   let ignore_m = ignore_m
 *   let join = join
 *   let bind = bind
 *   let ( >>= ) t f = bind t ~f
 *   let return = return
 *   let all = all
 *   let all_unit = all_unit
 * end *)


(* module SuiteMnd = struct
 *
 *   type 'a m = 'a suite
 *
 *   let pure = singleton
 *
 *   let rec bind s f =
 *     match s with
 *     | Emp -> Emp
 *     | Ext (s',x) -> append (bind s' f) (f x)
 *
 * end
 *
 * module SuiteTraverse(A: Applicative) = struct
 *
 *   type 'a t = 'a suite
 *   type 'a m = 'a A.t
 *
 *   open ApplicativeSyntax(A)
 *
 *   let rec traverse f s =
 *     match s with
 *     | Emp -> A.pure Emp
 *     | Ext (s',x) ->
 *       let+ y = f x
 *       and+ t = traverse f s' in
 *       Ext (t,y)
 *
 * end *)

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

open Fmt

let rec pp_suite ?emp:(pp_emp=nop) ?sep:(pp_sep=sp) pp_el ppf s =
  match s with
  | Emp -> pp_emp ppf ()
  | Ext (Emp,el) ->
    pf ppf "%a" pp_el el
  | Ext (s',el) ->
    pf ppf "%a%a%a" (pp_suite ~emp:pp_emp ~sep:pp_sep pp_el) s'
      pp_sep () pp_el el
