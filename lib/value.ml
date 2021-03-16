(*****************************************************************************)
(*                                                                           *)
(*                                   Values                                  *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Expr     
open Term
open Suite
open Syntax

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)
    
type value =
  | FlexV of mvar * spine
  | RigidV of lvl * spine
  | TopV of name * spine * value 
  | LamV of name * icit * closure
  | PiV of name * icit * value * closure
  | QuotV of quot_cmd * spine * value 
  | ObjV of value
  | HomV of value * value * value
  | CohV of value * spine
  | CylV of value * value * value
  | ArrV of value
  | CatV
  | TypV 

and spine =
  | EmpSp
  | AppSp of spine * value * icit
  | BaseSp of spine
  | LidSp of spine
  | CoreSp of spine

and top_env = (name * value) suite
and loc_env = value suite
and closure =
  | Closure of top_env * loc_env * term

let varV k = RigidV (k,EmpSp)
  
(*****************************************************************************)
(*                        Value Syntax Implementation                        *)
(*****************************************************************************)

(* module ValueSyntax = struct
 *   
 *   type s = value
 *   let lift _ v = v
 *   let cat = CatV
 *   let obj c = ObjV c
 *   let hom c s t = HomV (c,s,t)
 *   let var _ l = RigidV (l,EmpSp)
 *   let coh g a =  ??? 
 *   let app u v ict = appV (u,v,ict)
 * 
 *   let pd_vars _ pd =
 *     Pd.pd_lvl_map pd (fun _ l -> RigidV (l,EmpSp))
 *       
 * end *)

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
  | QuotV (cmd,sp,_) ->
    pf ppf "`[ %a ] %a" pp_quot_cmd cmd pp_spine sp 
  | ObjV c ->
    pf ppf "[%a]" pp_value c
  | HomV (_,s,t) ->
    pf ppf "%a => %a" pp_value s pp_value t
  | CohV (v,sp) -> 
    pf ppf "coh @[%a@] %a" 
      pp_value v pp_spine sp
  | CylV (b,l,c) ->
    pf ppf "[| %a | %a | %a |]"
      pp_value b pp_value l pp_value c
  | ArrV c ->
    pf ppf "Arr %a" pp_value c
  | CatV -> pf ppf "Cat"
  | TypV -> pf ppf "U"

and pp_spine ppf sp =
  match sp with
  | EmpSp -> ()
  | AppSp (sp',v,Expl) ->
    pf ppf "%a %a" pp_spine sp' pp_value v
  | AppSp (sp',v,Impl) ->
    pf ppf "%a {%a}" pp_spine sp' pp_value v
  | BaseSp sp' -> 
    pf ppf "base %a" pp_spine sp'
  | LidSp sp' ->
    pf ppf "lid %a" pp_spine sp'
  | CoreSp sp' ->
    pf ppf "core %a" pp_spine sp'

let pp_top_env = hovbox (pp_suite (parens (pair ~sep:(any " : ") string pp_value)))
let pp_loc_env = hovbox (pp_suite ~sep:comma pp_value)

