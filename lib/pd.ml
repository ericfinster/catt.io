(*****************************************************************************)
(*                                                                           *)
(*                               Batanin Trees                               *)
(*                                                                           *)
(*****************************************************************************)

type 'a pd =
  | Br of 'a * ('a * 'a pd) list

let rec map_pd f pd =
  match pd with
  | Br (a , brs) ->
    let loop (a, p) = (f a , map_pd f p) in
    Br (f a , List.map loop brs)

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

let ichg = Br ("x", [("y", Br ("f", [("g", Br("a", []));
                                     ("h", Br("b", []))]));
                     ("z", Br ("i", [("j", Br("c", []));
                                     ("k", Br("d", []))]))])

(*****************************************************************************)
(*                             Monadic Structure                             *)
(*****************************************************************************)

(* Here we'd like to implement the (partial) join operation on Batanin trees *)
