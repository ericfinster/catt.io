(*****************************************************************************)
(*                                                                           *)
(*                              User Expressions                             *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Pd     
open Suite

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type icit =
  | Impl
  | Expl

type name = string

type 'a tele = (name * icit * 'a) suite

type quot_cmd =
  | UComp of unit pd 
  | CompSeq of int list
        
type expr =
  | VarE of name
  | LamE of name * icit * expr
  | AppE of expr * expr * icit
  | PiE of name * icit * expr * expr
  | QuotE of quot_cmd
  | ObjE of expr
  | HomE of expr * expr * expr
  | CohE of expr tele * expr
  | CylE of expr * expr * expr
  | BaseE of expr
  | LidE of expr
  | CoreE of expr 
  | ArrE of expr
  | CatE
  | TypE
  | HoleE

type defn =
  | TermDef of name * expr tele * expr * expr
  | CohDef of name * expr tele * expr

(*****************************************************************************)
(*                Generic Pasting Diagram to Telescope Routine               *)
(*****************************************************************************)

let pd_to_tele mk_cat mk_obj mk_hom mk_nm mk_var mk_base_cat pd =

  let rec pd_to_tele_br tl cat src tgt k br =
    match br with
    | Br (l,brs) ->
      let cat' = mk_hom cat src tgt in
      let ict = if (Suite.is_empty brs) then Expl else Impl in
      let (tl',_,k') = pd_to_tele_brs (Ext (tl,(mk_nm l k,ict,mk_obj cat')))
          cat' (mk_var l k) (k+1) brs in 
      (tl',tgt,k')

  and pd_to_tele_brs tl cat src k brs =
    match brs with
    | Emp -> (tl,src,k)
    | Ext (brs',(l,br)) ->
      let (tl',src',k') = pd_to_tele_brs tl cat src k brs' in
      pd_to_tele_br (Ext (tl',(mk_nm l k',Impl,mk_obj cat))) cat src' (mk_var l k') (k'+1) br 

  in match pd with
  | Br (l,brs) ->
    let ict = if (Suite.is_empty brs) then Expl else Impl in
    let (tl,_,_) = pd_to_tele_brs
        (Emp |> ("C",Impl,mk_cat) |> (mk_nm l 1,ict,mk_obj mk_base_cat))
        (mk_base_cat) (mk_var l 1) 2 brs in tl

let pd_to_expr_tele : string pd -> expr tele = fun pd ->
  let mk_cat = CatE in 
  let mk_obj c = ObjE c in 
  let mk_hom c s t = HomE (c,s,t) in 
  let mk_nm l _ = l in 
  let mk_var l _ = VarE l in 
  let mk_base_cat = VarE "C" in 
  pd_to_tele mk_cat mk_obj mk_hom mk_nm mk_var mk_base_cat pd 

(*****************************************************************************)
(*                        Expr Tele to Pasting Diagram                       *)
(*****************************************************************************)

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
    (* pr "Trying pasting context: @[<hov>%a@]@," (pp_suite pp_value) loc; *)
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

let pp_tele pp_el ppf tl =
  let pp_trpl ppf (nm,ict,t) =
    match ict with
    | Expl -> pf ppf "(%s : %a)" nm pp_el t
    | Impl -> pf ppf "{%s : %a}" nm pp_el t
  in pp_suite pp_trpl ppf tl 

let rec pp_expr_gen show_imp ppf expr =
  let ppe = pp_expr_gen show_imp in 
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
    pf ppf "%a %a" ppe u pp_v v
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
  | QuotE _ -> pf ppf "quot"
  | ObjE e -> pf ppf "[%a]" ppe e
  | HomE (_,s,t) ->
    (* pf ppf "%a | %a => %a" ppe c ppe s ppe t *)
    pf ppf "%a => %a" ppe s ppe t
  | CohE (g,a) ->
    (match expr_tele_to_pd g with
     | Ok (pd,_,_,_,_) ->
       pf ppf "@[<hov>@[<hov>coh [ %a : @]@[<hov>%a ]@]@]"
         (pp_pd string) pd ppe a
     | Error _ -> 
       pf ppf "coh [ %a : %a ]" (pp_tele ppe) g ppe a)
   | CylE (b,l,c) ->
    pf ppf "[| %a | %a | %a |]" ppe b ppe l ppe c 
  | BaseE c ->
    pf ppf "base %a" ppe c
  | LidE c ->
    pf ppf "lid %a" ppe c
  | CoreE c ->
    pf ppf "core %a" ppe c 
  | ArrE c ->
    pf ppf "Arr %a" ppe c
  | CatE -> string ppf "Cat"
  | TypE -> string ppf "U"
  | HoleE -> string ppf "_"

let pp_expr = pp_expr_gen false
let pp_expr_with_impl = pp_expr_gen true
