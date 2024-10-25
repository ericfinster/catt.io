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
  | StarT
  | CatT
  | ObjT of term
  | ArrT of term
  | HomT of term * term * term

  (* Coherences *)
  | UCompT of ucmp_desc
  | CohT of nm_ict pd * term * term * term

  | CVarT 

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
  | StarT -> StarT
  | CatT -> CatT

  | UCompT pd -> UCompT pd
  | CohT (pd,c,s,t) -> CohT (pd,c,s,t)
  | CVarT -> CVarT 

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

  | StarT -> StarE
  | CatT -> CatE
  | ArrT c -> ArrE (tte nms c)
  | ObjT c -> ObjE (tte nms c)
  | HomT (c,s,t) ->
    HomE (tte nms c, tte nms s, tte nms t)

  | UCompT pd -> UCompE pd
  | CohT (pd,c,s,t) ->
    let g = ExprPdUtil.nm_ict_pd_to_tele pd in
    fold_accum_cont g nms
      (fun (nm,_,_) nms' -> ((),Ext (nms',nm)))
      (fun _ nms' ->
         let c' = tte nms' c in
         let s' = tte nms' s in
         let t' = tte nms' t in
         CohE (g,c',s',t'))

  | CVarT -> CVarE 

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

  | StarT -> pf ppf "*"
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

  | CohT (pd,c,s,t) ->
    pf ppf "@[coh [ @[%a@] :@;@[%a@]@;|> @[@[%a@] =>@;@[%a@]@] ]@]"
      (pp_pd string) (map_pd pd ~f:fst)
      ppt c ppt s ppt t
  | CVarT -> pf ppf "\u{25CF}"       

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
  | ArrT c -> free_vars k c
  | StarT -> fvs_empty
  | CatT -> fvs_empty
  | TypT -> fvs_empty
  | MetaT _ -> fvs_empty
  | InsMetaT _ -> fvs_empty
  | CVarT -> fvs_empty

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
  | CohT (pd,c,s,t) ->
    CohT (pd,c,s,t)
  | ArrT c -> ArrT (ss c)
  | StarT -> StarT
  | CatT -> CatT
  | TypT -> TypT
  | MetaT m -> MetaT m
  | InsMetaT m -> InsMetaT m
  | CVarT -> CVarT 

(*****************************************************************************)
(*                             Term Pd Conversion                            *)
(*****************************************************************************)

module TermPdSyntax = struct

  type s = term

  let star = StarT
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

let string_pd_to_term_tele (pd : string pd) : term tele =
  TermPdUtil.string_pd_to_tele pd

(*****************************************************************************)
(*                         Term Syntax Implmentations                        *)
(*****************************************************************************)

module TermCohSyntax = struct
  include TermPdSyntax

  module T = TermPdUtil

  let app u v ict = AppT (u,v,ict)
  let coh pd c s t = CohT (pd,c,s,t)
  let disc_coh pd =
    let lams = fold_right (labels pd) (VarT 0)
        (fun (nm,ict) tm ->
           LamT (nm,ict,tm))
    in lams

end

module TermCylSyntax = struct
  include TermCohSyntax

  let arr e = ArrT e

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

let term_str_ucomp (pd : string pd) : term =
  TermUtil.str_ucomp pd

let term_ucomp (pd : 'a pd) : term =
  TermUtil.gen_ucomp pd

let rec strip_names_tm t =
  match t with
  | LamT (nm,ict,t) -> LamT ("",ict,strip_names_tm t)
  | PiT (nm,ict,u,v) -> PiT ("",ict,strip_names_tm u, strip_names_tm v)
  | ObjT t -> ObjT (strip_names_tm t)
  | HomT (c,s,t) -> HomT (strip_names_tm c, strip_names_tm s, strip_names_tm t)
  | AppT (u,v,ict) -> AppT (strip_names_tm u, strip_names_tm v, ict)
  | CohT (pd,c,s,t) -> CohT (map_pd pd ~f:(fun (_,ict) -> ("",ict)), strip_names_tm c, strip_names_tm s, strip_names_tm t)
  | s -> s

let alpha_equiv s t = Poly.(=) (strip_names_tm s) (strip_names_tm t)

let rec top_levelify' top name t =
  let tl = top_levelify' top name in
  match t with
  | LamT (nm,ict,t) -> LamT (nm,ict,tl t)
  | AppT (u,v,ict) -> AppT (tl u, tl v, ict)
  | PiT(nm,ict,u,v) -> PiT (nm,ict,tl u,tl v)
  | ObjT c -> ObjT (tl c)
  | HomT (c,s,t) -> HomT(tl c, tl s, tl t)
  | CohT(pd,c,s,t) ->
     if alpha_equiv (CohT(pd,c,s,t)) (TermUtil.ucomp_coh pd)
     then UCompT (UnitPd (map_pd pd ~f:(fun _ -> ())))
     else let t' = CohT(pd,tl c, tl s, tl t) in
          (try TopT (assoc_with_comp alpha_equiv t' (! top))
          with Lookup_error ->
            let new_name = Fmt.str "def%d" (! name) in
            name := ! name + 1;
            top := Ext (! top, (t',new_name));
            TopT new_name)

  | s -> s


let top_levelify top v =
  let top_ref : ((term * name) suite) ref = ref top in
  let next_name : int ref = ref 0 in
  (!top_ref,top_levelify' top_ref next_name v)
