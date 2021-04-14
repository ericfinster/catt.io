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
  | CohT of nm_ict * nm_ict pd * term * term * term
  | CylCohT of nm_ict * nm_ict pd * term * term disc * term disc

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
  | CohT (cnm,pd,c,s,t) -> CohT (cnm,pd,c,s,t)
  | CylCohT (cn,pd,c,s,t) -> CylCohT (cn,pd,c,s,t)

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
  | CohT (cn,pd,c,s,t) ->
    let g = ExprPdUtil.nm_ict_pd_to_tele cn pd in
    fold_accum_cont g nms
      (fun (nm,_,_) nms' -> ((),Ext (nms',nm)))
      (fun _ nms' ->
         let c' = tte nms' c in
         let s' = tte nms' s in
         let t' = tte nms' t in
         CohE (g,c',s',t'))
  | CylCohT (cn,pd,c,s,t) ->
    let g = ExprPdUtil.nm_ict_pd_to_tele cn pd in
    fold_accum_cont g nms
      (fun (nm,_,_) nms' -> ((),Ext (nms',nm)))
      (fun _ nms' ->
         let c' = tte nms' c in
         let s' = map_disc ~f:(tte nms') s in
         let t' = map_disc ~f:(tte nms') t in
         CylCohE (g,c',s',t'))

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

let rec pp_term_gen ?si:(si=false) ppf tm =
  let ppt = pp_term_gen ~si:si in 
  match tm with
  | VarT i -> int ppf i
  | TopT nm -> string ppf nm
  | LamT (nm,Impl,t) ->
    pf ppf "\\{%s}. %a" nm ppt t
  | LamT (nm,Expl,t) ->
    pf ppf "\\%s. %a" nm ppt t
  | AppT (u,v,Impl) ->
    if si then
      pf ppf "%a {%a}" ppt u ppt v
    else
      pf ppf "%a" ppt u
  | AppT (u,v,Expl) ->
    (* Need's a generic lookahead for parens routine ... *)
    let pp_v = if (is_app_tm v) then
        parens ppt
      else ppt in
    pf ppf "%a@;%a" ppt u pp_v v
  | PiT (nm,Impl,a,p) ->
    pf ppf "{%s : %a}@;-> %a" nm
      ppt a ppt p
  | PiT (nm,Expl,a,p) when Poly.(=) nm "" ->
    let pp_a = if (is_pi_tm a) then
        parens ppt
      else ppt in
    pf ppf "%a@;-> %a"
      pp_a a ppt p
  | PiT (nm,Expl,a,p) ->
    pf ppf "(%s : %a)@;-> %a" nm
      ppt a ppt p
  | MetaT _ -> pf ppf "_"
  (* Again, misses some implicit information ... *)
  | InsMetaT _ -> pf ppf "*_*"
  | TypT -> pf ppf "U"

  | CatT -> pf ppf "Cat"
  | ObjT c ->
    pf ppf "[%a]" ppt c
  | HomT (_,s,t) ->
    (* pf ppf "@[%a@] |@, @[%a => %a@]" ppt c ppt s ppt t *)
    pf ppf "@[%a@] =>@;@[%a@]" ppt s ppt t
  | ArrT c -> pf ppf "Arr %a" ppt c

  | UCompT (UnitPd pd) ->
    pf ppf "ucomp [ %a ]" pp_tr pd
  | UCompT (DimSeq ds) ->
    pf ppf "ucomp [ %a ]" (list int) ds

  | CohT ((cn,_),pd,c,s,t) ->
    pf ppf "@[coh [ %s @[%a@] :@;@[%a@]@;|> @[@[%a@] =>@;@[%a@]@] ]@]" cn
      (pp_pd string) (map_pd pd ~f:fst)
      ppt c ppt s ppt t

  | CylCohT ((cn,_),pd,c,s,t) ->
    pf ppf "@[cylcoh [ %s @[%a@] :@;@[%a@]@;|> @[@[%a@] =>@;@[%a@]@] ]@]" cn
      (pp_pd string) (map_pd pd ~f:fst)
      ppt c (pp_disc ppt) s (pp_disc ppt) t

  | BaseT c -> pf ppf "base %a" ppt c
  | LidT c -> pf ppf "lid %a" ppt c
  | CoreT c -> pf ppf "core %a" ppt c
  | CylT (b,l,c) ->
    pf ppf "[| %a | %a | %a |]" ppt b ppt l ppt c


let pp_term = pp_term_gen ~si:false

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
  | CohT _ -> fvs_empty
  | CylCohT _ -> fvs_empty
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
(*                            Simple Substitutions                           *)
(*****************************************************************************)

let rec simple_sub (k : lvl) (tm : term) (sub : term option suite) : term =
  let ss u = simple_sub k u sub in 
  match tm with 
  | VarT i when i >= k ->
    begin match db_get (i - k) sub with
      | Some t -> t
      | None -> failwith (Fmt.str "undefined term in sub (i=%d) (k=%d)" i k)
    end
  | VarT i -> VarT i
  | TopT nm -> TopT nm
  | LamT (nm,ict,bdy) ->
    let bdy' = simple_sub (k+1) bdy sub in 
    LamT (nm,ict,bdy')
  | AppT (u,v,ict) ->
    AppT (ss u, ss v, ict)
  | PiT (nm,ict,a,b) ->
    let b' = simple_sub (k+1) b sub in 
    PiT (nm,ict,ss a,b')
  | ObjT c -> ObjT (ss c)
  | HomT (c,s,t) ->
    HomT (ss c, ss s, ss t)
  | UCompT ud -> UCompT ud
  | CohT (cn,pd,c,s,t) ->
    CohT (cn,pd,c,s,t)
  | CylCohT (cn,pd,c,s,t) -> 
    CylCohT (cn,pd,c,s,t)
  | CylT (b,l,c) ->
    CylT (ss b, ss l, ss c)
  | BaseT c -> BaseT (ss c)
  | LidT c -> LidT (ss c)
  | CoreT c -> CoreT (ss c)
  | ArrT c -> ArrT (ss c)
  | CatT -> CatT
  | TypT -> TypT
  | MetaT m -> MetaT m
  | InsMetaT m -> InsMetaT m

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

  let pp_dbg = pp_term 

  let strengthen (src: bool) (dim : int) (pd : 'a pd) : term -> term =
    
    let bpd = Pd.truncate src dim pd in
    let blvl = pd_length bpd in
    
    (* log_msg "-------------------";
     * log_msg "strengthening ...";
     * log_val "pd" pd Pd.pp_tr;
     * log_val "bpd" bpd Pd.pp_tr;
     * log_val "blvl" blvl Fmt.int; *)
    
    let sub = Pd.fold_pd_with_type pd (Ext (Emp, Some (VarT blvl)) , blvl - 1)
        (fun _ ty (s,i) ->
           let incld = (Ext (s,Some (VarT i)),i-1) in 
           let excld = (Ext (s,None),i) in
           match ty with
           | SrcCell d ->
             if src then 
               (if (d > dim) then excld else incld)
             else
               (if (d < dim) then incld else excld)
           | TgtCell d ->
             if src then 
               (if (d < dim) then incld else excld)
             else
               (if (d > dim) then excld else incld)
           | IntCell d ->
             if (d < dim) then incld else excld
           | LocMaxCell d ->
             if (d <= dim) then incld else excld
        ) in 

    (* log_val "sub" (fst sub) (pp_suite (Fmt.option ~none:(any "*") pp_term));
     * log_msg "-------------------"; *)
      
    fun tm -> simple_sub 0 tm (fst sub)
  
end

module TermPdUtil = PdUtil(TermPdSyntax)

let string_pd_to_term_tele (c : string) (pd : string pd) : term tele =
  TermPdUtil.string_pd_to_tele c pd

(*****************************************************************************)
(*                         Term Syntax Implmentations                        *)
(*****************************************************************************)

module TermCohSyntax = struct
  include TermPdSyntax

  module T = TermPdUtil

  let app u v ict = AppT (u,v,ict)
  let coh cn pd c s t = CohT (cn,pd,c,s,t)
  let disc_coh cn pd =
    let lams = fold_right (labels pd) (VarT 0)
        (fun (nm,ict) tm ->
           LamT (nm,ict,tm))
    in LamT (fst cn, snd cn, lams)

end

module TermCylSyntax = struct
  include TermCohSyntax

  let arr e = ArrT e
  let cyl b l c = CylT (b,l,c)
  let base e = BaseT e
  let lid e = LidT e
  let core e = CoreT e

end

module TermSyntax = struct
  include TermCylSyntax
  let lam nm ict bdy = LamT (nm,ict,bdy)
  let pi nm ict dom cod = PiT (nm,ict,dom,cod)
  let pp_s = pp_term 
end

module TermUtil = struct
  include PdUtil(TermPdSyntax)
  include CohUtil(TermCohSyntax)
  include SyntaxUtil(TermSyntax)
end

let term_str_ucomp (c : string) (pd : string pd) : term =
  TermUtil.str_ucomp c pd

let term_ucomp (pd : 'a pd) : term =
  TermUtil.gen_ucomp pd



