(*****************************************************************************)
(*                                                                           *)
(*                            Suites (snoc lists)                            *)
(*                                                                           *)
(*****************************************************************************)

open Mtl
       
type 'a suite =
  | Emp
  | Ext of 'a suite * 'a 

let (|>) a b = Ext (a, b)

let rec length s =
  match s with
  | Emp -> 0
  | Ext (s',_) -> length s' + 1

let rec map f s =
  match s with
  | Emp -> Emp
  | Ext (s',x) -> map f s' |> f x 

let rec fold_left f a s =
  match s with
  | Emp -> a
  | Ext (s',x) -> f (fold_left f a s') x

let rec fold_right f s a =
  match s with
  | Emp -> a
  | Ext (s',x) -> fold_right f s' (f x a)

let rec append s t =
  match t with
  | Emp -> s
  | Ext (t',x) -> Ext (append s t',x)

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

let zip_with_idx s =
  let rec zip_with_idx_pr s =
    match s with
    | Emp -> (Emp,0)
    | Ext (s',x) ->
      let (s'', i) = zip_with_idx_pr s' in
      (Ext (s'',(i,x)), i+1)
  in fst (zip_with_idx_pr s)
    
let rec first s =
  match s with
  | Emp -> raise Not_found
  | Ext (Emp,x) -> x
  | Ext (s',_) -> first s'

let last s =
  match s with
  | Emp -> raise Not_found
  | Ext (_,x) -> x

let rec assoc k s =
  match s with
  | Emp -> raise Not_found
  | Ext (s',(k',v)) ->
    if (k = k') then v
    else assoc k s'

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
  | Emp -> raise Not_found
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
  | Emp -> raise Not_found
  | Ext (s'',x) -> (s'',x::r)

let split_at k s =
  let d = length s in
  grab (d-k) s 

(*****************************************************************************)
(*                                   Zipper                                  *)
(*****************************************************************************)

open MonadSyntax(ErrMnd(struct type t = string end))
    
type 'a suite_zip = ('a suite * 'a * 'a list)

let close (l,a,r) =
  append_list (Ext(l,a)) r

let open_rightmost s =
  match s with
  | Emp -> Fail "Empty suite on open"
  | Ext (s',a) -> Ok (s',a,[])

let move_left (l,a,r) =
  match l with
  | Emp -> Fail "No left element"
  | Ext (l',a') -> Ok (l',a',a::r)

let move_right (l,a,r) =
  match r with
  | [] ->  Fail "No right element"
  | a'::r' -> Ok (Ext (l,a),a',r')

let rec move_left_n n z =
  if (n<=0) then Ok z else
    move_left z >>= move_left_n (n-1)

let open_leftmost s =
  let n = length s in
  open_rightmost s >>= move_left_n (n-1)

let open_at k s =
  let l = length s in
  if (k+1>l) then
    Fail "Out of range"
  else open_rightmost s >>= move_left_n (l-k-1)

(*****************************************************************************)
(*                               Instances                                   *)
(*****************************************************************************)

module SuiteMnd = struct

  type 'a m = 'a suite

  let pure = singleton

  let rec bind s f =
    match s with
    | Emp -> Emp
    | Ext (s',x) -> append (bind s' f) (f x)
  
end

module SuiteTraverse(A: Applicative) = struct

  type 'a t = 'a suite
  type 'a m = 'a A.t

  open ApplicativeSyntax(A)

  let rec traverse f s =
    match s with
    | Emp -> A.pure Emp
    | Ext (s',x) ->
      let+ y = f x
      and+ t = traverse f s' in
      Ext (t,y)
    
end

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

open Format

let rec pp_print_suite_custom emp b sep f ppf s =
  match s with
  | Emp -> pp_print_string ppf emp
  | Ext (Emp,a) ->
    if b then 
      fprintf ppf "%s@,%s%a" emp sep f a
    else
      fprintf ppf "%s@,%a" emp f a
  | Ext (s',a) ->
    pp_print_suite_custom emp b sep f ppf s'; 
    fprintf ppf "@,%s%a" sep f a

let pp_print_suite f ppf s =
  pp_print_suite_custom "Emp" true "|>" f ppf s

let pp_print_suite_horiz f ppf s =
  pp_print_suite_custom "" false "," f ppf s
    
let rec pp_print_suite_plain f ppf s =
  match s with
  | Emp -> ()
  | Ext (s',a) ->
    fprintf ppf "%a%a" (pp_print_suite_plain f) s' f a
