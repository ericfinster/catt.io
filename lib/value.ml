(*****************************************************************************)
(*                                                                           *)
(*                                   Values                                  *)
(*                                                                           *)
(*****************************************************************************)

open Pd
open Fmt
open Term
open Suite
open Syntax

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type value =

  (* Primitives *)
  | FlexV of mvar * spine   (* A term stuck because head is meta *)
  | RigidV of lvl * spine   (* A term stuck because head is bound variable *)
  | TopV of name * spine * value
  | LamV of name * icit * closure
  | PiV of name * icit * value * closure
  | TypV

  (* Categories *)
  | CatV
  | ObjV of value
  | HomV of value * value * value
  | ArrV of value

  (* Coherences *)
  | UCompV of ucmp_desc * value * spine
  | CohV of (name * icit) * (name * icit) pd * value * value * value * spine

and spine =
  | EmpSp
  | AppSp of spine * value * icit

and top_env = (name * value) suite
and loc_env = value suite
and closure =
  | Closure of top_env * loc_env * term

let varV k = RigidV (k,EmpSp)

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let rec pp_value ppf v =
  match v with
  | FlexV (m,sp) ->
    pf ppf "?%d %a" m pp_spine sp
  | RigidV (i,EmpSp) -> pf ppf "%d" i
  | RigidV (i,sp) -> pf ppf "%d %a" i pp_spine sp
  | TopV (nm,sp,_) ->
    pf ppf "%s %a" nm pp_spine sp
  | LamV (nm,Expl,Closure (_,_,bdy)) ->
    pf ppf "\\%s.<%a>" nm pp_term bdy
  | LamV (nm,Impl,Closure (_,_,bdy)) ->
    pf ppf "\\{%s}.<%a>" nm pp_term bdy
  | PiV (nm,Expl,a,Closure (_,_,bdy)) ->
    pf ppf "(%s : %a) -> <%a>" nm
      pp_value a pp_term bdy
  | PiV (nm,Impl,a,Closure (_,_,bdy)) ->
    pf ppf "{%s : %a} -> <%a>" nm
      pp_value a pp_term bdy
  | TypV -> pf ppf "U"

  | CatV -> pf ppf "Cat"
  | ObjV c ->
    pf ppf "[%a]" pp_value c
  | ArrV c ->
    pf ppf "Arr %a" pp_value c
  | HomV (c,s,t) ->
    pf ppf "%a | %a => %a" pp_value c pp_value s pp_value t

  | UCompV (uc,_,sp) ->
    pf ppf "ucomp [ %a ] %a"
      pp_ucmp_desc uc pp_spine sp

  | CohV ((cn,_),pd,c,s,t,sp) ->
    pf ppf "@[coh [ %s @[%a@] :@;@[%a@]@;|> @[@[%a@] =>@;@[%a@]@] @[%a] ]@]" cn
      (pp_pd string) (map_pd pd ~f:fst)
      pp_value c pp_value s pp_value t pp_spine sp
      
and pp_spine ppf sp =
  match sp with
  | EmpSp -> ()
  | AppSp (sp',v,Expl) ->
    pf ppf "%a %a" pp_spine sp' pp_value v
  | AppSp (sp',v,Impl) ->
    pf ppf "%a {%a}" pp_spine sp' pp_value v

let pp_top_env = hovbox (pp_suite (parens (pair ~sep:(any " : ") string pp_value)))
let pp_loc_env = hovbox (pp_suite ~sep:comma pp_value)
