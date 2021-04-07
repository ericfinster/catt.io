(*****************************************************************************)
(*                                                                           *)
(*                              User Expressions                             *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Pd
open Suite
open Syntax

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type expr =

  (* Type theory primitives *)
  | VarE of name
  | LamE of name * icit * expr
  | AppE of expr * expr * icit
  | PiE of name * icit * expr * expr
  | HoleE
  | TypE

  (* Categories *)
  | CatE
  | ObjE of expr
  | HomE of expr * expr * expr
  | ArrE of expr

  (* Forms of coherences *)
  | UCompE of ucmp_desc
  | CohE of expr tele * expr * expr * expr
  | CylCohE of expr tele * expr * expr disc * expr disc

  (* cylinders *)
  | CylE of expr * expr * expr
  | BaseE of expr
  | LidE of expr
  | CoreE of expr

(* This probably belongs elsewhere .... *)
type defn =
  | TermDef of name * expr tele * expr * expr
  | CohDef of name * expr tele * expr * expr * expr
  | CylCohDef of name * expr tele * expr * expr disc * expr disc

(*****************************************************************************)
(*                         Pretty Printing Raw Syntax                        *)
(*****************************************************************************)

let is_app e =
  match e with
  | AppE (_, _, _) -> true
  | _ -> false

let is_pi e =
  match e with
  | PiE (_,_,_,_) -> true
  | _ -> false

let arr_parens e =
  match e with
  | ArrE _ -> true
  | HomE _ -> true
  | _ -> false

let tele_to_pd_dummy _ =
  Error "dummy"

let rec pp_expr_gen ?tpd:(tpd = tele_to_pd_dummy)
    ~si:show_imp ~fh:full_homs ~pc:pd_ctxs ppf expr =
  let ppe = pp_expr_gen ~tpd:tpd ~si:show_imp ~fh:full_homs ~pc:pd_ctxs in
  match expr with
  | VarE nm -> string ppf nm
  | LamE (nm,Impl,bdy) -> pf ppf "\\{%s}. %a" nm ppe bdy
  | LamE (nm,Expl,bdy) -> pf ppf "\\%s. %a" nm ppe bdy
  | AppE (u, v, Impl) ->
    if show_imp then
      pf ppf "%a {%a}" ppe u ppe v
    else
      pf ppf "%a" ppe u
  | AppE (u, v, Expl) ->
    let pp_v = if (is_app v) then
        parens ppe
      else ppe in
    pf ppf "%a@, %a" ppe u pp_v v
  | PiE (nm,Impl,dom,cod) ->
    if (is_pi cod) then
      pf ppf "{%s : %a}@, %a" nm
        ppe dom ppe cod
    else
      pf ppf "{%s : %a}@, -> %a" nm
        ppe dom ppe cod
  | PiE (nm,Expl,a,b) when Poly.(=) nm "" ->
    let pp_a = if (is_pi a) then
        parens ppe
      else ppe in
    pf ppf "%a -> %a"
      pp_a a ppe b
  | PiE (nm,Expl,dom,cod) ->
    if (is_pi cod) then
      pf ppf "(%s : %a)@, %a" nm
        ppe dom ppe cod
    else
      pf ppf "(%s : %a)@, -> %a" nm
        ppe dom ppe cod
  | TypE -> string ppf "U"
  | HoleE -> string ppf "_"

  | CatE -> string ppf "Cat"
  | ArrE c ->
    if (arr_parens c) then
      pf ppf "Arr (%a)" ppe c
    else
      pf ppf "Arr %a" ppe c
  | ObjE e -> pf ppf "[@[<hov>%a@]]" ppe e
  | HomE (c,s,t) ->
    if full_homs then
      pf ppf "@[%a@] |@;@[<hov>@[%a@] =>@;@[%a@]@]" ppe c ppe s ppe t
    else
      pf ppf "@[%a@] =>@;@[%a@]" ppe s ppe t

  | UCompE (UnitPd pd) ->
    pf ppf "ucomp [ %a ]" pp_tr pd
  | UCompE (DimSeq ds) ->
    pf ppf "ucomp [ %a ]" (list int) ds
  | CohE (g,c,s,t) ->

    begin match tpd g with
      | Ok (cn,pd) ->
        if full_homs then
          pf ppf "coh [@[ %s @[%a@] :@;@[%a@]@;|> @[%a =>@;%a @]@]]"
            cn (pp_pd string) pd ppe c ppe s ppe t
        else
          pf ppf "coh [@[ %s @[%a@] :@;@[<hov>@[%a@] =>@;@[%a@]@]@]]"
            cn (pp_pd string) pd ppe s ppe t
      | Error _ ->
        if full_homs then
          pf ppf "@[coh [ @[%a@] :@;@[%a@]@;|> %a =>@;%a ]@]"
            (pp_tele ppe) g ppe c ppe s ppe t
        else
          pf ppf "@[coh [ @[%a@] :@;@[<hov>@[%a@] =>@;@[%a@]@]]@]"
            (pp_tele ppe) g ppe s ppe t
    end

  | CylCohE (g,c,s,t) ->
    pf ppf "cylcoh [ %a : %a |> %a => %a ]"
      (pp_tele ppe) g ppe c (pp_disc ppe) s (pp_disc ppe) t

  | BaseE c ->
    pf ppf "base %a" ppe c
  | LidE c ->
    pf ppf "lid %a" ppe c
  | CoreE c ->
    pf ppf "core %a" ppe c
  | CylE (b,l,c) ->
    pf ppf "cyl @[<hov>@[(%a)@]@;@[(%a)@]@;@[(%a)@]@]"
      ppe b ppe l ppe c

let pp_expr_dummy = pp_expr_gen ~tpd:tele_to_pd_dummy ~si:true ~fh:true ~pc:true

(*****************************************************************************)
(*                             Expr Pd Conversion                            *)
(*****************************************************************************)

module ExprPdSyntax = struct

  type s = expr

  let cat = CatE
  let obj c = ObjE c
  let hom c s t = HomE (c,s,t)

  let match_hom e =
    match e with
    | HomE (c,s,t) -> Some (c,s,t)
    | _ -> None

  let match_obj e =
    match e with
    | ObjE c -> Some c
    | _ -> None

  let lift _ t = t
  let var _ _ nm = VarE nm

  let pp_dbg = pp_expr_dummy

end

module ExprPdUtil =
  PdUtil(ExprPdSyntax)

let string_pd_to_expr_tele (c : string) (pd : string pd) : expr tele =
  ExprPdUtil.string_pd_to_tele c pd

(*****************************************************************************)
(*                          Matching pretty printers                         *)
(*****************************************************************************)

let pp_expr = pp_expr_gen
    ~tpd:ExprPdUtil.tele_to_name_pd
    ~si:false ~fh:false ~pc:true

let pp_expr_with_impl = pp_expr_gen
    ~tpd:ExprPdUtil.tele_to_name_pd
    ~si:true ~fh:true ~pc:true

(*****************************************************************************)
(*                         Expr Syntax Implmentations                        *)
(*****************************************************************************)

module ExprCohSyntax = struct
  include ExprPdSyntax

  module E = ExprPdUtil

  let app u v ict = AppE (u,v,ict)
  let coh cn pd c s t =
    let g = E.nm_ict_pd_to_tele cn pd in
    CohE (g,c,s,t)
  let disc_coh cn pd =
    let lbls = labels pd in
    let (hnm,_) = head lbls in
    let lams = fold_right lbls (VarE hnm)
        (fun (nm,ict) e ->
           LamE (nm,ict,e))
    in LamE (fst cn, snd cn, lams)

end

module ExprCylSyntax = struct
  include ExprCohSyntax

  let arr e = ArrE e
  let cyl b l c = CylE (b,l,c)
  let base e = BaseE e
  let lid e = LidE e
  let core e = CoreE e

end

module ExprSyntax = struct
  include ExprCylSyntax
  let lam nm ict bdy = LamE (nm,ict,bdy)
  let pi nm ict dom cod = PiE (nm,ict,dom,cod)
  let pp_s = pp_expr
end

module ExprUtil = struct
  include PdUtil(ExprPdSyntax)
  include CohUtil(ExprCohSyntax)
  include SyntaxUtil(ExprSyntax)
end

let expr_str_ucomp (c : string) (pd : string pd) : expr =
  ExprUtil.str_ucomp c pd

let expr_ucomp (pd : 'a pd) : expr =
  ExprUtil.gen_ucomp pd
