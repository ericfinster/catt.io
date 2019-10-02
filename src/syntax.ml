(*
 * syntax.ml - syntactic definitions
 *)

(* Raw, user level expressions *)

type expr =
  | ObjE
  | ArrowE of expr * expr
  | VarE of string
  | CohE of (string * expr) list * expr
  | CompE of (string * expr) list * expr
  | AppE of expr * expr

(* Commands *)
type cmd =
  | Def of string * (string * expr) list * expr
  | Let of string * (string * expr) list * expr * expr
          
(* Our semantic type domain allows for function
 * types.  These will be used internally to type
 * coherences an lets, but no exposed Pi types 
 * exist.
 *)

type dom =
  
  (* Types *)
  | ObjD
  | ArrowD of dom * dom * dom
  | PiD of dom * (dom -> dom)

  (* Terms *)
  | VarD of int
  | AppD of dom * dom 
         
