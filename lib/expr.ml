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
  | CohE of expr pd_desc * expr * expr * expr 
  | CylCohE of expr pd_desc * expr * expr disc * expr disc

  (* cylinders *)
  | CylE of expr * expr * expr
  | BaseE of expr
  | LidE of expr
  | CoreE of expr 

(* This probably belongs elsewhere .... *)
type defn =
  | TermDef of name * expr tele * expr * expr
  | CohDef of name * expr pd_desc * expr * expr * expr 
  (* | CohDef of name * expr pd_desc * expr * expr disc * expr disc *)

(*****************************************************************************)
(*                        Expr Tele to Pasting Diagram                       *)
(*****************************************************************************)

(* FIXME: This is now generic. Use that version in pp .... *)

let (let*) m f = Base.Result.bind m ~f 

let rec unhom e =
  match e with
  | HomE (c,_,_) ->
    let (cat,dim) = unhom c in
    (cat,dim+1)
  | _ -> (e, 0)

let unobj e =
  match e with
  | ObjE c -> Ok c
  | _ -> Error "not an object type"

let rec ith_tgt i ty tm =
  if (i = 0) then Ok (ty, tm) else
    match ty with
    | HomE (c,_,t) ->
      ith_tgt (i-1) c t
    | _ -> Error "No target"

let expr_tele_to_pd tl = 
  let rec go l tl =
    (* pr "Trying pasting context: @[%a@]@," (pp_suite pp_value) loc; *)
    match tl with
    | Emp -> Error "Empty context is not a pasting diagram"
    | Ext(Emp,_) -> Error "Singleton context is not a pasting diagram"
                      
    | Ext(Ext(Emp,(c,_,CatE)),(x,_,ObjE (VarE c'))) ->
      if (Poly.(<>) c c') then
        Error "Incorrect base category"
      else
        Ok (Pd.Br (x,Emp),VarE c,VarE x,2,0)
        
    | Ext(Ext(loc',(t,_,ObjE tty)),(f,_,ObjE fty)) -> 
      
      let* (pd,sty,stm,k,dim) = go (l+2) loc' in
      let (_,tdim) = unhom tty in
      let codim = dim - tdim in
      let* (sty',stm') = ith_tgt codim sty stm in 
      
      if (Poly.(<>) sty' tty) then
        Error "incompatible source and target types"
      else let ety = HomE (sty',stm',VarE t) in
        if (Poly.(<>) ety fty) then 
          Error "incorrect filling type"
        else let* pd' = Pd.insert_right pd tdim t
                 (Pd.Br (f, Emp)) in
          Ok (pd', fty, VarE f, k+2, tdim+1)
        
    | _ -> Error "malformed pasting context"
             
  in go 0 tl

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

let rec pp_expr_gen ~si:show_imp ~fh:full_homs ~pc:pd_ctxs ppf expr =
  let ppe = pp_expr_gen ~si:show_imp ~fh:full_homs ~pc:pd_ctxs in 
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
    pf ppf "{%s : %a} -> %a" nm
      ppe dom ppe cod
  | PiE (nm,Expl,a,b) when Poly.(=) nm "" ->
    let pp_a = if (is_pi a) then
        parens ppe
      else ppe in 
    pf ppf "%a -> %a" 
      pp_a a ppe b
  | PiE (nm,Expl,dom,cod) ->
    pf ppf "(%s : %a) -> %a" nm
      ppe dom ppe cod
  | TypE -> string ppf "U"
  | HoleE -> string ppf "_"

  | CatE -> string ppf "Cat"
  | ArrE c ->
    pf ppf "Arr %a" ppe c
  | ObjE e -> pf ppf "[%a]" ppe e
  | HomE (c,s,t) ->
    if full_homs then 
      pf ppf "%a | %a => %a" ppe c ppe s ppe t
    else
      pf ppf "@[%a@] =>@;@[%a@]" ppe s ppe t

  | UCompE (UnitPd pd) ->
    pf ppf "ucomp [ %a ]" pp_tr pd
  | UCompE (DimSeq ds) ->
    pf ppf "ucomp [ %a ]" (list int) ds
  | CohE (TelePd g,c,s,t) ->
    pf ppf "@[coh [ @[%a@] : @[%a@] |> %a => %a ]@]"
      (pp_tele ppe) g ppe c ppe s ppe t
  | CohE (TreePd (_,g),c,s,t) ->
    pf ppf "@[coh [ @[%a@] : @[%a@] |> %a => %a ]@]"
      pp_tr g ppe c ppe s ppe t
  | CylCohE (TelePd g,c,s,t) ->
    pf ppf "cylcoh [ %a : %a |> %a => %a ]"
      (pp_tele ppe) g ppe c (pp_disc ppe) s (pp_disc ppe) t
  | CylCohE (TreePd (_,g),c,s,t) ->
    pf ppf "cylcoh [ %a : %a |> %a => %a ]"
      pp_tr g ppe c (pp_disc ppe) s (pp_disc ppe) t

  | BaseE c ->
    pf ppf "base %a" ppe c
  | LidE c ->
    pf ppf "lid %a" ppe c
  | CoreE c ->
    pf ppf "core %a" ppe c 
  | CylE (b,l,c) ->
    pf ppf "[| %a | %a | %a |]" ppe b ppe l ppe c 

let pp_expr = pp_expr_gen ~si:false ~fh:true ~pc:true
let pp_expr_with_impl = pp_expr_gen ~si:true ~fh:true ~pc:true



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

  let pp = pp_expr
    
end

module ExprPdConv = PdConversion(ExprPdSyntax)

let string_pd_to_expr_tele (pd : string pd) : expr tele = 
  ExprPdConv.pd_to_tele (VarE "C")
    (* FIXME! Use a better map to decide implicitness *)
    (map_pd pd ~f:(fun s -> (s,Impl,VarE s)))

(*****************************************************************************)
(*                      Expression Syntax Implementation                     *)
(*****************************************************************************)
              
module ExprSyntax = struct
  include ExprPdSyntax

  let lam nm ict bdy = LamE (nm,ict,bdy)
  let pi nm ict dom cod = PiE (nm,ict,dom,cod)
  let app u v ict = AppE (u,v,ict)
  let coh g c s t = CohE (TelePd g,c,s,t)
  
end

module ExprUtil = SyntaxUtil(ExprSyntax)

let str_expr_ucomp_coh : string pd -> expr = fun pd ->
  ExprUtil.ucomp_coh (Pd.map_pd pd ~f:(fun s -> VarE s))

let str_expr_ucomp : string pd -> expr = fun pd ->
  ExprUtil.ucomp (VarE "C") (Pd.map_pd pd ~f:(fun s -> VarE s))

let expr_app_args = ExprUtil.app_args

let ucomp_coh_expr : 'a pd -> expr = fun pd ->
  ExprUtil.ucomp_coh pd 
