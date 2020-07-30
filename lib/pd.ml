(*****************************************************************************)
(*                                                                           *)
(*                               Batanin Trees                               *)
(*                                                                           *)
(*****************************************************************************)

open Cheshire.Functor
       
type 'a pd =
  | Br of 'a * ('a * 'a pd) list

let lmap = List.map

let rec dim pd =
  match pd with
  | Br (_,brs) ->
    let bdims = lmap (fun (_,b) -> dim b) brs in 
    let maxdim = List.fold_left max (-1) bdims in
    1 + maxdim 

let decorations pd =
  match pd with
  | Br (a,brs) -> a :: lmap fst brs 

let rec chop d pd =
  match pd with
  | Br (a,brs) ->
    if (d <= 0) then Br (a,[])
    else Br (a, lmap (fun (l,b) -> (l,chop (d-1) b)) brs)

(*****************************************************************************)
(*                              Functor Instance                             *)
(*****************************************************************************)
    
module PdFunctor : Functor with type 'a t := 'a pd =
  MakeFunctor(struct

    type 'a t = 'a pd
        
    let rec map f pd =
      match pd with
      | Br (a , brs) ->
        let loop (a, p) = (f a , map f p) in
        Br (f a , lmap loop brs)

  end)

let map_pd = PdFunctor.map
              
(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)
      
open Format

let rec pplist f ppf l = 
  match l with
  | [] -> ()
  | x::[] -> fprintf ppf "%a" f x
  | x::xs ->
    fprintf ppf "%a@," f x ;
    pplist f ppf xs

let print_enclosed f ppf l =
  pp_print_string ppf "[" ; 
  pp_open_vbox ppf 0 ;
  pplist f ppf l ;
  pp_close_box ppf () ; 
  pp_print_string ppf "]"

let rec pp_print_pd ppf pd =
  match pd with
  | Br (s , brs) ->
    fprintf ppf "Br (%s, %a)" s (print_enclosed pp_print_branch) brs

and pp_print_branch ppf (s, pd) =
  fprintf ppf "(%s, %a)" s pp_print_pd pd

let print_pd pd =
  pp_print_pd std_formatter pd ;
  pp_print_newline std_formatter

(*****************************************************************************)
(*                             Monadic Structure                             *)
(*****************************************************************************)

open Cheshire.Err
open ErrMonad.MonadSyntax

let rec match_zip_with f l l' =
  match l,l' with
  | [],[] -> Ok []
  | (x::xs),(y::ys) ->
    let* res = match_zip_with f xs ys in
    Ok ((f x y)::res)
  | _ -> Fail "Mismatch"

let rec zip l l' =
  match l,l' with
  | [],_ -> []
  | _,[] -> []
  | (x::xs),(y::ys) ->
    (x,y)::(zip xs ys)

(* This version makes no well-typing checks ... *)
let rec merge d p q =
  match p,q with
  | Br (_,bas), Br (l,bbs) ->
    if (d <= 0) then
      Br (l, (bas @ bbs))
    else
      let loop ((_,p'),(l,q')) = (l, merge (d-1) p' q') in 
      let rbrs = lmap loop (zip bas bbs) in
      Br (l, rbrs)

(* Okay, here's a first guess ... *)
let rec join_pd d pd =
  match pd with
  | Br (p,brs) ->
    let loop (_,b) = join_pd (d+1) b in
    let res = lmap loop brs in
    List.fold_left (merge d) p res 
    
(*****************************************************************************)
(*                                  Examples                                 *)
(*****************************************************************************)
      
let obj = Br ("x", [])
let arr = Br ("x", [("y", Br ("f", []))])

let comp2 = Br ("x", [("y", Br ("f", []));
                      ("z", Br ("g", []))])
    
let comp3 = Br ("x", [("y", Br ("f", []));
                      ("z", Br ("g", []));
                      ("w", Br ("h", []))])

let vert2 = Br ("x", [("y", Br ("f", [("g", Br("a", []));
                                      ("h", Br("b", []))]))])

let horiz2 = Br ("x", [("y", Br ("f", [("g", Br("a", []))]));
                       ("z", Br ("h", [("k", Br("b", []))]))])
  
let ichg = Br ("x", [("y", Br ("f", [("g", Br("a", []));
                                     ("h", Br("b", []))]));
                     ("z", Br ("i", [("j", Br("c", []));
                                     ("k", Br("d", []))]))])

let blank pd = map_pd (fun _ -> ()) pd
let subst pd sub = map_pd (fun id -> List.assoc id sub) pd    

let example =
  (subst comp2
     [ ("x" , obj);
       ("y" , obj);
       ("z" , obj);
       ("f" , comp2);
       ("g" , comp2)
     ])

let example2 =
  (subst vert2
     [
       ("x" , obj);
       ("y" , obj);
       ("f" , comp2);
       ("g" , comp2);
       ("h" , comp2);
       ("a" , horiz2);
       ("b" , horiz2)
     ])

