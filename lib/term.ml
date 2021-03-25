(*****************************************************************************)
(*                                                                           *)
(*                              Internal Syntax                              *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Pd
open Base
open Expr
open Suite
open Syntax
    
(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type term =

  (* Primitives *)
  | VarT of idx
  | TopT of name 
  | LamT of name * icit * term
  | AppT of term * term * icit
  | PiT of name * icit * term * term
  | MetaT of mvar
  | InsMetaT of mvar 
  | TypT

  (* Categories *)
  | CatT
  | ObjT of term
  | ArrT of term
  | HomT of term * term * term

  (* Coherences *)
  | UCompT of ucmp_desc 
  | CohT of term tele * term * term * term 
  | CylCohT of term tele * term * term disc * term disc

  (* Cylinders *)
  | CylT of term * term * term
  | BaseT of term
  | LidT of term
  | CoreT of term 

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
  | MetaT m -> MetaT m
  | InsMetaT m -> InsMetaT m 
  | TypT -> TypT

  | ObjT tm -> ObjT (lft tm)
  | HomT (c,s,t) -> HomT (lft c, lft s, lft t)
  | ArrT c -> ArrT (lft c)
  | CatT -> CatT

  | UCompT pd -> UCompT pd
  | CohT (g,c,s,t) -> 
    tele_fold_with_idx g l
      (fun tm l' -> db_lift_by l' k tm)
      (fun g' l' ->
         let c' = db_lift_by l' k c in
         let s' = db_lift_by l' k s in
         let t' = db_lift_by l' k t in 
         CohT (g',c',s',t'))
  | CylCohT (g,c,s,t) ->
    tele_fold_with_idx g l
      (fun tm l' -> db_lift_by l' k tm)
      (fun g' l' ->
         let c' = db_lift_by l' k c in
         let s' = map_disc s ~f:(db_lift_by l' k) in
         let t' = map_disc t ~f:(db_lift_by l' k) in 
         CylCohT (g',c',s',t'))

  | BaseT t -> BaseT (lft t)
  | LidT t -> LidT (lft t)
  | CoreT t -> CoreT (lft t)
  | CylT (b,l,c) -> CylT (lft b, lft l, lft c)

let db_lift l t = db_lift_by l 1 t

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
  | MetaT _ -> HoleE
  (* Somewhat dubious, since we lose the implicit application ... *)
  | InsMetaT _ -> HoleE
  | TypT -> TypE

  | CatT -> CatE 
  | ArrT c -> ArrE (tte nms c)
  | ObjT c -> ObjE (tte nms c)
  | HomT (c,s,t) ->
    HomE (tte nms c, tte nms s, tte nms t)

  | UCompT pd -> UCompE pd
  | CohT (g,c,s,t) -> 
    fold_accum_cont g nms
      (fun (nm,ict,tm) nms' ->
         ((nm,ict,tte nms' tm), Ext (nms',nm)))
      (fun g' nms' ->
         let c' = tte nms' c in
         let s' = tte nms' s in
         let t' = tte nms' t in
         CohE (TelePd g',c',s',t'))
  | CylCohT (g,c,s,t) ->
    fold_accum_cont g nms
      (fun (nm,ict,tm) nms' ->
         ((nm,ict,tte nms' tm), Ext (nms',nm)))
      (fun g' nms' ->
         let c' = tte nms' c in
         let s' = map_disc ~f:(tte nms') s in
         let t' = map_disc ~f:(tte nms') t in
         CylCohE (TelePd g',c',s',t'))

  | BaseT c -> BaseE (tte nms c)
  | LidT c -> LidE (tte nms c)
  | CoreT c -> CoreE (tte nms c)
  | CylT (b,l,c) ->
    CylE (tte nms b, tte nms l, tte nms c)

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
    (* Need's a generic lookahead for parens routine ... *)
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
  | MetaT _ -> pf ppf "_"
  (* Again, misses some implicit information ... *)
  | InsMetaT _ -> pf ppf "*_*"
  | TypT -> pf ppf "U"

  | CatT -> pf ppf "Cat"
  | ObjT c ->
    pf ppf "[%a]" pp_term c
  | HomT (c,s,t) ->
    pf ppf "%a | %a => %a" pp_term c pp_term s pp_term t
  | ArrT c -> pf ppf "Arr %a" pp_term c

  | UCompT (UnitPd pd) ->
    pf ppf "ucomp [ %a ]" pp_tr pd
  | UCompT (DimSeq ds) ->
    pf ppf "ucomp [ %a ]" (list int) ds
  | CohT (g,c,s,t) ->
    pf ppf "coh [ %a : %a |> %a <=> %a ]"
      (pp_tele pp_term) g pp_term c
      pp_term s
      pp_term t
  | CylCohT (g,c,s,t) ->
    pf ppf "cylcoh [ %a : %a |> %a <=> %a ]"
      (pp_tele pp_term) g pp_term c
      (pp_disc pp_term) s
      (pp_disc pp_term) t

  | BaseT c -> pf ppf "base %a" pp_term c
  | LidT c -> pf ppf "lid %a" pp_term c
  | CoreT c -> pf ppf "core %a" pp_term c
  | CylT (b,l,c) ->
    pf ppf "[| %a | %a | %a |]" pp_term b pp_term l pp_term c

(*****************************************************************************)
(*                               Free Variables                              *)
(*****************************************************************************)

let fvs_empty = Set.empty (module Int)
let fvs_singleton k = Set.singleton (module Int) k
    
let rec free_vars k tm =
  match tm with
  | VarT i when i >= k -> fvs_singleton i 
  | VarT _ -> fvs_empty
  | TopT _ -> fvs_empty
  | LamT (_,_,bdy) -> free_vars (k+1) bdy
  | AppT (u,v,_) ->
    Set.union (free_vars k u) (free_vars k v)
  | PiT (_,_,a,b) ->
    Set.union (free_vars k a) (free_vars (k+1) b)
  | ObjT c -> free_vars k c
  | HomT (c,s,t) ->
    Set.union (free_vars k c) (Set.union (free_vars k s) (free_vars k t))
  | UCompT _ -> fvs_empty
  | CohT (g,c,s,t) ->
    let rec go k g =
      match g with
      | Emp -> free_vars k (HomT (c,s,t))
      | Ext (g',_) -> go (k+1) g'
    in go k g
  | CylCohT _ -> failwith "fvs cylcoh"
  | CylT (b,l,c) ->
    Set.union (free_vars k b) (Set.union (free_vars k l) (free_vars k c))
  | BaseT c -> free_vars k c
  | LidT c -> free_vars k c
  | CoreT c -> free_vars k c
  | ArrT c -> free_vars k c
  | CatT -> fvs_empty
  | TypT -> fvs_empty
  | MetaT _ -> fvs_empty
  | InsMetaT _ -> fvs_empty

(*****************************************************************************)
(*                         Term Syntax Implementation                        *)
(*****************************************************************************)

module TermSyntax = struct
  type s = term
  let lift i t = db_lift_by 0 i t
  let cat = CatT
  let obj c = ObjT c
  let hom c s t = HomT (c,s,t)
  let var k l _ = VarT (lvl_to_idx k l)
  let lam nm ict bdy = LamT (nm,ict,bdy)
  let pi nm ict dom cod = PiT (nm,ict,dom,cod)
  let coh g c s t = CohT (g,c,s,t)
  let app u v ict = AppT (u,v,ict)
  let pp = pp_term
  let nm_of k _ = str "x%d" (k-1)
  let fresh_cat k = ("C", VarT k)
end

module TermUtil = SyntaxUtil(TermSyntax)

let term_app_args = TermUtil.app_args

let pd_to_term_tele : 'a Pd.pd -> term tele = fun pd ->
  (* let k = length (Pd.labels pd) in *)
  let fr_pd = Pd.pd_idx_map pd (fun _ i -> VarT i) in
  TermUtil.pd_to_tele fr_pd

let term_ucomp_coh : 'a Pd.pd -> term = fun pd ->
  TermUtil.ucomp_coh pd

(*****************************************************************************)
(*                             Term Pd Conversion                            *)
(*****************************************************************************)

module TermPdSyntax = struct

  type s = term
    
  let cat = CatT
  let obj c = ObjT c
  let hom c s t = HomT (c,s,t)
  
  let match_hom e =
    match e with
    | HomT (c,s,t) -> Some (c,s,t)
    | _ -> None

  let match_obj e =
    match e with
    | ObjT c -> Some c
    | _ -> None 

  let lift i t = db_lift_by 0 i t
  let var k l _ = VarT (lvl_to_idx k l)

  let pp = pp_term
    
end

module TermPdConv = PdConversion(TermPdSyntax)

let term_fixup (pd : string pd) : (term decl) pd =
  (pd_idx_map pd (fun s _ -> (s,Impl,VarT 0)))
  
let string_pd_to_term_tele (pd : string pd) : term tele = 
  TermPdConv.pd_to_tele (VarT 0) (term_fixup pd)

