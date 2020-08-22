(*****************************************************************************)
(*                                                                           *)
(*                               Batanin Trees                               *)
(*                                                                           *)
(*****************************************************************************)

open Suite
    
type 'a pd =
  | Br of 'a * ('a * 'a pd) suite

let rec dim_pd pd =
  match pd with
  | Br (_,brs) ->
    let f d (_,b) = max d (dim_pd b) in 
    1 + fold_left f (-1) brs 

(* Truncate to the provided dimension.  The boolean
   flag dir is true for the source direction, false
   for the target *)

let rec truncate dir d pd =
  match pd with
  | Br (a, brs) ->
    if (d <= 0) then
      (
        if dir then Br (a, Emp)
        else let a' = fold_left (fun _ (y,_) -> y) a brs in 
          Br (a', Emp)
      )
    else Br (a, map (fun (l,b) -> (l,truncate dir (d-1) b)) brs)

let rec insert pd d lbl nbr =
  let open Cheshire.Err in
  let open ErrMonad.MonadSyntax in 
  match pd with
  | Br (a,brs) ->
    if (d <= 0) then
      Ok (Br (a, Ext(brs,(lbl,nbr))))
    else match brs with
      | Emp -> Fail "Depth overflow"
      | Ext(bs,(b,br)) ->
        let* rbr = insert br (d-1) lbl nbr in
        Ok (Br (a,Ext(bs,(b,rbr))))

let rec append_leaves pd lvs =
  match pd with
  | Br (l,Emp) -> Ext (lvs,l)
  | Br (_,bs) -> 
    let open Suite.SuiteMonad in
    bs >>= (fun (_,b) -> leaves b)

and leaves pd = append_leaves pd Emp

let rec labels pd =
  match pd with
  | Br (l,brs) ->
    let open Suite.SuiteMonad in
    append (singleton l)
      (brs >>= (fun (bl,b) -> append (singleton bl) (labels b)))

(*****************************************************************************)
(*                              Instances                                    *)
(*****************************************************************************)

open Cheshire.Functor
open Cheshire.Applicative

module PdFunctor : Functor with type 'a t := 'a pd =
  MakeFunctor(struct

    type 'a t = 'a pd
        
    let rec map f pd =
      match pd with
      | Br (a, brs) ->
        let fm (l, b) = (f l, map f b) in
        Br (f a, Suite.map fm brs)

  end)

let map_pd = PdFunctor.map

module PdTraverse(A : Applicative) = struct

  type 'a t = 'a pd
  type 'a m = 'a A.t

  open A.ApplicativeSyntax

  module ST = SuiteTraverse(A)

  let rec traverse f pd =
    match pd with
    | Br (a,abrs) ->
      let tr (l,b) =
        let+ l' = f l
        and+ b' = traverse f b
        in (l',b') in 
      let+ b = f a
      and+ bbrs = ST.traverse tr abrs in
      Br (b,bbrs)
        
end

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

open Format

let rec pp_print_pd f ppf pd =
  match pd with
  | Br (s,brs) ->
    let ps ppf (l,b) = fprintf ppf "(%a, %a)" f l (pp_print_pd f) b in 
    fprintf ppf "Br (%a, @[<v>%a@])" f s (pp_print_suite ps) brs

let print_pd pd =
  pp_print_pd pp_print_string std_formatter pd ;
  pp_print_newline std_formatter

(*****************************************************************************)
(*                      Substitution of Pasting Diagrams                     *)
(*****************************************************************************)

let rec merge d p q =
  match p,q with
  | Br (l,bas), Br (_,bbs) ->
    if (d <= 0) then
      Br (l, append bas bbs)
    else
      let mm ((l,p'),(_,q')) = (l,merge (d-1) p' q') in 
      Br (l, map mm (zip bas bbs))

let rec join_pd d pd =
  match pd with
  | Br (p,brs) ->
    let jr (_,b) = join_pd (d+1) b in
    fold_left (merge d) p (map jr brs)

let rec disc n =
  if (n <= 0) then Br ((), Emp)
  else Br ((), Ext (Emp, ((), disc (n-1))))

let blank pd = map_pd (fun _ -> ()) pd
let subst pd sub = map_pd (fun id -> assoc id sub) pd

(* let comp2 = Br ("x", Emp
 *                      |> ("y", Br ("f", Emp))
 *                      |> ("z", Br ("g", Emp))) *)


(* let example5 =
 *   subst comp2
 *     (Emp
 *      |> ("x", mk_obj "x")
 *      |> ("y", mk_obj "y")
 *      |> ("f", mk_arr "x" "y" "f")
 *      |> ("z", mk_obj "z")
 *      |> ("g", mk_arr "y" "z" "g")) *)




(*****************************************************************************)
(*                                  Examples                                 *)
(*****************************************************************************)

let obj = Br ("x", Emp)
    
let arr = Br ("x", Emp
                   |> ("y", Br ("f", Emp)))

let mk_obj x = Br (x, Emp)
let mk_arr x y f = Br (x,Emp
                         |> (y, Br (f, Emp)))
                   
let comp2 = Br ("x", Emp
                     |> ("y", Br ("f", Emp))
                     |> ("z", Br ("g", Emp)))
    
let comp3 = Br ("x", Emp
                     |> ("y", Br ("f", Emp))
                     |> ("z", Br ("g", Emp))
                     |> ("w", Br ("h", Emp)))

let vert2 = Br ("x", Emp
                     |> ("y", Br ("f", Emp
                                       |> ("g", Br ("a", Emp))
                                       |> ("h", Br ("b", Emp)))))

let horiz2 = Br ("x", Emp
                      |> ("y", Br ("f", Emp
                                        |> ("g", Br ("a", Emp))))
                      |> ("z", Br ("h", Emp
                                        |> ("k", Br ("a", Emp)))))

let ichg = Br ("x", Emp
                    |> ("y", Br ("f", Emp
                                      |> ("g", Br ("a", Emp))
                                      |> ("h", Br ("b", Emp))))
                    |> ("z", Br ("i", Emp
                                      |> ("j", Br ("c", Emp))
                                      |> ("k", Br ("d", Emp)))))

let vert2whiskl = Br ("x", Emp
                           |> ("y", Br ("f", Emp
                                             |> ("g", Br ("a", Emp))
                                             |> ("h", Br ("b", Emp))))
                           |> ("z", Br ("k", Emp)))

let disc2 = Br ("x", Emp
                     |> ("y", Br ("f", Emp
                                       |> ("g", Br ("a", Emp)))))

let ichgmidwhisk =  Br ("x", Emp
                             |> ("y", Br ("f", Emp
                                               |> ("g", Br ("a", Emp))
                                               |> ("h", Br ("b", Emp))))
                             |> ("z", Br ("i", Emp))
                             |> ("w", Br ("j", Emp
                                               |> ("k", Br ("c", Emp))
                                               |> ("l", Br ("d", Emp)))))

(*****************************************************************************)
(*                           Substitution Examples                           *)
(*****************************************************************************)
    
let example =
  subst comp2
    (Emp
     |> ("x", obj)
     |> ("y", obj)
     |> ("z", obj)
     |> ("f", comp2)
     |> ("g", comp2))

let example2 =
  subst vert2
    (Emp
     |> ("x" , obj)
     |> ("y" , obj)
     |> ("f" , comp2)
     |> ("g" , comp2)
     |> ("h" , comp2)
     |> ("a" , horiz2)
     |> ("b" , horiz2))

let example3 =
  subst ichgmidwhisk
    (Emp
     |> ("x", obj)
     |> ("y", obj)
     |> ("f", comp2)
     |> ("g", comp2)
     |> ("a", vert2whiskl)
     |> ("h", comp2)
     |> ("b", ichg)
     |> ("z", obj)
     |> ("i", comp3)
     |> ("w", obj)
     |> ("j", arr)
     |> ("k", arr)
     |> ("c", disc2)
     |> ("l", arr)
     |> ("d", vert2))

let example4 =
  subst arr
    (Emp
     |> ("x", Br("x",Emp))
     |> ("y", Br("z",Emp))
     |> ("f", comp2))

let example5 =
  subst comp2
    (Emp
     |> ("x", mk_obj "x")
     |> ("y", mk_obj "y")
     |> ("f", mk_arr "x" "y" "f")
     |> ("z", mk_obj "z")
     |> ("g", mk_arr "y" "z" "g"))


