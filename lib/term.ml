(*****************************************************************************)
(*                                                                           *)
(*                              Internal Syntax                              *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Expr
open Suite

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type term =
  | VarT of idx
  | TopT of name 
  | LamT of name * icit * term
  | AppT of term * term * icit
  | PiT of name * icit * term * term
  | QuotT of quot_cmd * term
  | ObjT of term
  | HomT of term * term * term
  | CohT of term tele * term
  | CylT of term * term * term
  | BaseT of term
  | LidT of term
  | CoreT of term 
  | ArrT of term
  | CatT
  | TypT
  | MetaT of mvar
  | InsMetaT of mvar 

(*****************************************************************************)
(*                              DeBrujin Lifting                             *)
(*****************************************************************************)

let rec db_lift_by l k tm =
  let lft = db_lift_by l k in 
  match tm with
  | VarT i ->
    if (i >= l) then VarT (k+i) else VarT i
  | TopT nm -> TopT nm
  | LamT (nm,ict,tm) ->
    LamT (nm, ict, db_lift_by (l+1) k tm)
  | AppT (u,v,ict) -> AppT (lft u, lft v, ict)
  | PiT (nm,ict,a,b) ->
    PiT (nm,ict,lft a, db_lift_by (l+1) k b)
  | QuotT (cmd,tm) -> QuotT (cmd, lft tm)
  | ObjT tm -> ObjT (lft tm)
  | HomT (c,s,t) -> HomT (lft c, lft s, lft t)
  | CohT (g,a) -> 

    let rec go g l m =
      match g with
      | Emp -> m Emp l 
      | Ext (g',(nm,ict,tm)) ->
        go g' l (fun rg rl ->
            let tm' = db_lift_by rl k tm in
            m (Ext (rg,(nm,ict,tm'))) (rl+1))

    in go g l (fun g' l' -> CohT (g', db_lift_by l' k a))

  | CylT (b,l,c) -> CylT (lft b, lft l, lft c)
  | BaseT t -> BaseT (lft t)
  | LidT t -> LidT (lft t)
  | CoreT t -> CoreT (lft t)
  | ArrT c -> ArrT (lft c)
  | CatT -> CatT
  | TypT -> TypT
  | MetaT m -> MetaT m
  | InsMetaT m -> InsMetaT m 

let db_lift l t = db_lift_by l 1 t

let lvl_to_idx k l = k - l - 1

(*****************************************************************************)
(*                            Terms to Expressions                           *)
(*****************************************************************************)

let rec term_to_expr nms tm =
  let tte = term_to_expr in 
  match tm with
  | VarT i ->
    let nm = db_get i nms in VarE nm
  | TopT nm -> VarE nm
  | LamT (nm,ict,bdy) ->
    LamE (nm, ict, tte (Ext (nms,nm)) bdy)
  | AppT (u,v,ict) ->
    AppE (tte nms u, tte nms v, ict)
  | PiT (nm,ict,a,b) ->
    PiE (nm, ict, tte nms a, tte (Ext (nms,nm)) b)
  | QuotT (cmd,_) -> QuotE cmd
  | ObjT c -> ObjE (tte nms c)
  | HomT (c,s,t) ->
    HomE (tte nms c, tte nms s, tte nms t)
  | CohT (g,a) ->

    let rec go g nms m =
      match g with
      | Emp -> m nms Emp
      | Ext (g',(nm,ict,ty)) ->
        go g' nms (fun nms' ge' ->
            let e = tte nms' ty in
            m (Ext (nms',nm))
              (Ext (ge',(nm,ict,e))))

    in go g nms (fun nms' ge' -> CohE (ge' , tte nms' a))

  | CylT (b,l,c) ->
    CylE (tte nms b, tte nms l, tte nms c)
  | BaseT c -> BaseE (tte nms c)
  | LidT c -> LidE (tte nms c)
  | CoreT c -> CoreE (tte nms c)
  | ArrT c -> ArrE (tte nms c)
  | CatT -> CatE 
  | TypT -> TypE
  | MetaT _ -> HoleE
  (* Somewhat dubious, since we lose the implicit application ... *)
  | InsMetaT _ -> HoleE

(*****************************************************************************)
(*                                 Telescopes                                *)
(*****************************************************************************)
    
let rec tele_to_pi tl ty =
  match tl with
  | Emp -> ty
  | Ext (tl',(nm,ict,ty_tm)) ->
    tele_to_pi tl' (PiT (nm,ict,ty_tm,ty))

let pi_to_tele ty =
  let rec go tl ty = 
    match ty with
    | PiT (nm,ict,a,b) ->
      go (Ext (tl,(nm,ict,a))) b
    | _ -> (tl,ty)
  in go Emp ty

(*****************************************************************************)
(*                       Pasting Diagrams to Telescopes                      *)
(*****************************************************************************)

(* module ExprGen = struct
 *   type s = expr
 *   let lift _ t = t
 *   let cat = CatE
 *   let obj c = ObjE c
 *   let var _ l = VarE (str "x%d" l)
 *   let hom c s t = HomE (c,s,t)
 *   let coh g a = CohE (g,a)
 *   let app u v ict = AppE (u,v,ict)
 *   let pd_vars k pd = pd_lvl_map pd 
 *       (fun _ k' -> VarE (str "x%d" (k+k')))
 * end *)

module TermGen = struct
  type s = term
  let lift i t = db_lift_by 0 i t
  let cat = CatT
  let obj c = ObjT c
  let hom c s t = HomT (c,s,t)
  let var k l = VarT (k - l + 1)
  let coh g a = CohT (g,a)
  let app u v ict = AppT (u,v,ict)

  let pd_vars _ pd =
    Pd.pd_idx_map pd (fun _ i -> VarT i)
      
end

let pd_to_term_tele : unit Pd.pd -> term tele = fun pd ->
  let open PdToTele(TermGen) in
  let nm_gen _ k = str "x%d" k in
  let var_gen _ _ = VarT 0 in
  pd_to_tele nm_gen var_gen (VarT 0) pd

let unbiased_comp_term : 'a Pd.pd -> term = fun pd ->
  let open UnbiasedComp(TermGen) in
  let nm_gen _ k = str "x%d" k in
  let var_gen _ _ = VarT 0 in
  unbiased_comp nm_gen var_gen (VarT 0) pd 

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)
    
let is_app_tm tm =
  match tm with
  | AppT (_,_,_) -> true
  | _ -> false

let is_pi_tm tm =
  match tm with
  | PiT (_,_,_,_) -> true
  | _ -> false
    
let rec pp_term ppf tm =
  match tm with
  | VarT i -> int ppf i
  | TopT nm -> string ppf nm 
  | LamT (nm,Impl,t) ->
    pf ppf "\\{%s}. %a" nm pp_term t
  | LamT (nm,Expl,t) ->
    pf ppf "\\%s. %a" nm pp_term t
  | AppT (u,v,Impl) ->
    pf ppf "%a {%a}" pp_term u pp_term v
  | AppT (u,v,Expl) ->
    let pp_v = if (is_app_tm v) then
        parens pp_term
      else pp_term in 
    pf ppf "%a %a" pp_term u pp_v v
  | PiT (nm,Impl,a,p) ->
    pf ppf "{%s : %a} -> %a" nm
      pp_term a pp_term p
  | PiT (nm,Expl,a,p) when Poly.(=) nm "" ->
    let pp_a = if (is_pi_tm a) then
        parens pp_term
      else pp_term in 
    pf ppf "%a -> %a" 
      pp_a a pp_term p
  | PiT (nm,Expl,a,p) ->
    pf ppf "(%s : %a) -> %a" nm
      pp_term a pp_term p
  | QuotT (cmd,_) ->
    pf ppf "`[ %a ]" pp_quot_cmd cmd
  | ObjT c ->
    pf ppf "[%a]" pp_term c
  | HomT (c,s,t) ->
    pf ppf "%a | %a => %a" pp_term c pp_term s pp_term t
  | CohT (g,a) ->
    pf ppf "coh @[[ %a : %a ]@]" (pp_tele pp_term) g pp_term a
  | CylT (b,l,c) ->
    pf ppf "[| %a | %a | %a |]" pp_term b pp_term l pp_term c
  | BaseT c -> pf ppf "base %a" pp_term c
  | LidT c -> pf ppf "lid %a" pp_term c
  | CoreT c -> pf ppf "core %a" pp_term c
  | ArrT c -> pf ppf "Arr %a" pp_term c
  | CatT -> pf ppf "Cat"
  | TypT -> pf ppf "U"
  | MetaT _ -> pf ppf "_"
  (* Again, misses some implicit information ... *)
  | InsMetaT _ -> pf ppf "*_*"
