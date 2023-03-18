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
open Base

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
  | StarV
  | CatV
  | ObjV of value
  | HomV of value * value * value
  | ArrV of value

  (* Coherences *)
  | UCompV of ucmp_desc * value * spine
  | CohV of (name * icit) pd * value * value * value * spine

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

  | StarV -> pf ppf "*"
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

  | CohV (pd,c,s,t,sp) ->
    pf ppf "@[coh [ %@[%a@] :@;@[%a@]@;|> @[@[%a@] =>@;@[%a@]@] @[%a] ]@]"
      (pp_pd string) (map_pd pd ~f:fst)
      pp_value c pp_value s pp_value t pp_spine sp

and pp_spine_gen ?sep:(sep=Fmt.sp) ppf sp =
  match sp with
  | EmpSp -> ()
  | AppSp (sp',v,Expl) ->
    pf ppf "%a%a(%a)" (pp_spine_gen ~sep:sep) sp' sep () pp_value v
  | AppSp (sp',v,Impl) ->
     pf ppf "%a%a{%a}" (pp_spine_gen ~sep:sep) sp' sep () pp_value v

and pp_spine ppf sp = pp_spine_gen ~sep:Fmt.sp ppf sp

let pp_top_env = hovbox (pp_suite (parens (pair ~sep:(any " : ") string pp_value)))
let pp_loc_env = hovbox (pp_suite ~sep:comma pp_value)

let rec sp_to_suite sp =
  let open Base.Result.Monad_infix in
  match sp with
  | EmpSp -> Ok (Emp)
  | AppSp (s,v,i) -> sp_to_suite s >>= fun s' -> Ok (Ext(s', (v,i)))

let rec suite_to_sp s =
  match s with
  | Emp -> EmpSp
  | Ext(s, (v,i)) -> AppSp (suite_to_sp s,v,i)

let rec map_sp sp ~f =
  match sp with
  | EmpSp -> EmpSp
  | AppSp (s,v,i) -> AppSp (map_sp s ~f, f v, i)

let rec fixup_impl v =
  match v with
  | FlexV (m, sp) -> FlexV (m, fixup_sp_impl sp)
  | RigidV (i, sp) -> RigidV (i, fixup_sp_impl sp)
  | TopV(nm,sp,v) -> TopV(nm,fixup_sp_impl sp, fixup_impl v)
  | ObjV c -> ObjV (fixup_impl c)
  | HomV (c,s,t) -> HomV (fixup_impl c, fixup_impl s, fixup_impl t)
  | UCompV (uc,v,sp) -> UCompV (uc,fixup_impl v, fixup_sp_impl sp)
  | CohV (pd,c,s,t,sp) ->
     let pd' = map_pd_lf_nd pd ~lf:(fun (x,_) -> (x,Expl)) ~nd:(fun (x,_) -> (x,Impl)) in
     (match (let* sp_suite = sp_to_suite sp in Ok (zip (map_suite ~f:fst sp_suite) (append (Ext(Emp,Impl)) (map_suite ~f:snd (labels pd'))))) with
     | Error _ -> CohV (pd,fixup_impl c, fixup_impl s, fixup_impl t, fixup_sp_impl sp)
     | Ok xs -> CohV (pd',fixup_impl c, fixup_impl s, fixup_impl t, fixup_sp_impl (suite_to_sp xs)))
  | v -> v

and fixup_sp_impl sp =
  match sp with
  | EmpSp -> EmpSp
  | AppSp (sp',v,ict) -> AppSp (fixup_sp_impl sp', fixup_impl v, ict)

(*****************************************************************************)
(*                         Value Syntax Implmentations                       *)
(*****************************************************************************)

module ValuePdSyntax = struct

  type s = value

  let star = StarV
  let obj c = ObjV c
  let hom c s t = HomV (c,s,t)

  let match_hom e =
    match e with
    | HomV (c,s,t) -> Some (c,s,t)
    | _ -> None

  let match_obj e =
    match e with
    | ObjV c -> Some c
    | _ -> None

  let lift _ t = t
  let var _ l _ = RigidV (l,EmpSp)

  let pp_dbg = pp_value
end

module ValuePdUtil = PdUtil(ValuePdSyntax)
