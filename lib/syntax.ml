(*****************************************************************************)
(*                                                                           *)
(*                        Generic Syntax Constructions                       *)
(*                                                                           *)
(*****************************************************************************)

open Suite
open Base
open Pd

(*****************************************************************************)
(*                             Basic Syntax Types                            *)
(*****************************************************************************)

type lvl = int
type idx = int
type mvar = int
type name = string

let lvl_to_idx k l = k - l - 1
let idx_to_lvl k i = k - i - 1

let idx_pd pd =
  map_pd_lvls pd 0
    ~f:(fun k l _ _ -> lvl_to_idx k l)

type perm = (lvl,lvl,Int.comparator_witness) Map.t

type icit =
  | Impl
  | Expl

type nm_ict = (name * icit)
type 'a decl = (name * icit * 'a)
type 'a tele = ('a decl) suite

type ucmp_desc =
  | UnitPd of unit pd
  | DimSeq of int list

let pp_ucmp_desc ppf uc =
  let open Fmt in
  match uc with
  | UnitPd pd -> pf ppf "%a" pp_tr pd
  | DimSeq ds -> pf ppf "%a" (list int) ds

let pp_ict ppf ict =
  match ict with
  | Impl -> Fmt.pf ppf "Impl"
  | Expl -> Fmt.pf ppf "Expl"

let pp_nm_ict ppf ni =
  let open Fmt in
  pf ppf "%a" (parens (pair ~sep:(any ",") string pp_ict)) ni

let ucmp_pd uc =
  match uc with
  | UnitPd pd -> pd
  | DimSeq ds -> comp_seq ds

(*****************************************************************************)
(*                             Logging functions                             *)
(*****************************************************************************)

let log_msg ?idt:(i=0) (s : string) =
  let indt = String.make i ' ' in
  Fmt.pr "@[<v>%s@,@]" (indt ^ s)

let log_val ?idt:(i=0) (s : string) (a : 'a) (pp : 'a Fmt.t) =
  let indt = String.make i ' ' in
  Fmt.pr "@[<v>%s: @[%a@]@,@]@," (indt ^ s) pp a

(*****************************************************************************)
(*                                 Telescopes                                *)
(*****************************************************************************)

let tele_fold_with_idx g l f =
  fold_accum_cont g l
    (fun (nm,ict,tm) l' ->
       ((nm,ict,f tm l') , l'+1))

let pp_tele pp_el ppf tl =
  let pp_trpl ppf (nm,ict,t) =
    match ict with
    | Expl -> Fmt.pf ppf "(%s : %a)" nm pp_el t
    | Impl -> Fmt.pf ppf "{%s : %a}" nm pp_el t
  in pp_suite pp_trpl ppf tl

(*****************************************************************************)
(*                         Pasting Diagram Conversion                        *)
(*****************************************************************************)

module type PdSyntax = sig

  type s

  val cat : s
  val obj : s -> s
  val hom : s -> s -> s -> s

  val match_hom : s -> (s * s * s) Option.t
  val match_obj : s -> s Option.t

  val lift : int -> s -> s
  val var : lvl -> lvl -> name -> s

  (* val strengthen : bool -> int -> 'a pd -> s -> s *)

  val pp_dbg : s Fmt.t

end

module PdUtil(P : PdSyntax) = struct
  include P

  let rec dim_ty c =
    match match_hom c with
    | None -> 0
    | Some (c,_,_) -> dim_ty c + 1

  let rec match_homs (c : s) : (s * s sph) =
    match match_hom c with
    | None -> (c,Emp)
    | Some (c',s,t) ->
      let (c'',sph) = match_homs c' in
      (c'', Ext (sph,(s,t)))

  let match_cat_type (c : s) : (s * s sph) Option.t =
    Base.Option.map (match_obj c) ~f:(match_homs)

  let rec sph_to_cat (c : s) (sph : s sph) : s =
    match sph with
    | Emp -> c
    | Ext (sph',(s,t)) ->
      hom (sph_to_cat c sph') s t

  let pd_to_tele ((cnm,cict) : (name * icit)) (pd : 'a pd)
      (lf : lvl -> 'a -> (name * icit))
      (nd : lvl -> 'a -> (name * icit)) : s tele =

    let rec do_br bc sph br tl lvl =
      match br with
      | Br (x,brs) ->
        let (nm,ict) = if (is_empty brs)
          then lf lvl x
          else nd lvl x in
        let sty = obj (sph_to_cat bc sph) in
        let tl' =  Ext (tl,(nm,ict,sty)) in
        let src = var (lvl+1) lvl nm in
        do_brs (lift 1 bc) (map_sph sph ~f:(lift 1)) src brs tl' (lvl+1)

    and do_brs bc sph src brs tl lvl =
      match brs with
      | Emp -> (tl, bc, lvl, src)
      | Ext (brs',(x,br)) ->
        let (tl',bc',lvl',src') = do_brs bc sph src brs' tl lvl in
        let sph' = map_sph sph ~f:(lift (lvl' - lvl)) in
        let tty = obj (sph_to_cat bc' sph') in
        let (nm,ict) = nd lvl x in
        let tgt = var (lvl+1) lvl nm in (* check lvl here! *)
        let (tl'',bc'',lvl'',_) =
          do_br (lift 1 bc')
            (Ext (map_sph sph' ~f:(lift 1),(lift 1 src',tgt)))
            br (Ext (tl',(nm,ict,tty))) (lvl'+1) in
        (tl'',bc'',lvl'',lift (lvl''-lvl'-1) tgt)

    in let (tl,_,_,_) = do_br (var 1 0 cnm) Emp pd (Ext (Emp,(cnm,cict,cat))) 1 in tl

  let nm_ict_pd_to_tele (c : (name * icit)) (pd : (name * icit) pd) : s tele =
    pd_to_tele c pd (fun _ ni -> ni) (fun _ ni -> ni)

  let string_pd_to_tele (cnm : name) (pd : name pd) : s tele =
    pd_to_tele (cnm,Impl) pd (fun _ nm -> (nm,Expl))
      (fun _ nm -> (nm,Impl))

  let fresh_pd_tele (pd : 'a pd) : s tele =
    let vn l = Fmt.str "x%d" l in
    pd_to_tele ("C",Impl) pd
      (fun l _ -> (vn l,Expl))
      (fun l _ -> (vn l,Impl))

  let tele_to_pd_fold (tl : s tele)
      (f : name -> icit -> lvl -> lvl -> s sph -> 'a)
    : ((name * icit) * 'a pd , string) Result.t =

    let (let*) m f = Base.Result.bind m ~f in

    let rec go (d : int) (tl : s tele) =
      match tl with
      | Emp -> Error "Empty context is not a pasting diagram"
      | Ext(Emp,_) -> Error "Singleton context is not a pasting diagram"

      | Ext(Ext(Emp,(cnm,cict,cty)),(onm,oict,oty)) ->

        let depth = d + 2 in
        let cvar = var 1 0 cnm in
        let svar = var 2 1 onm in

        if (Poly.(<>) cty cat) then
          Error "Pasting diagram does not start with an abstract category"
        else if (Poly.(<>) oty (obj cvar)) then
          Error "Initial object not in the correct category"
        else

          let olbl = f onm oict depth 1 Emp in

          Ok (Pd.Br (olbl,Emp), lift 1 cvar , Emp, svar, depth, 2, 0, cnm, cict)

      | Ext(Ext(tl',(tnm,tict,tty)),(fnm,fict,fty)) ->

        let* (pd,ctm,ssph,stm,dpth,lvl,dim,cnm,cict) = go (d + 2) tl' in

        let* (tcat,tsph) = Result.of_option (match_cat_type tty)
            ~error:"Target cell does not have category type." in

        let tdim = length tsph in
        let codim = dim - tdim in
        let (ssph',stm') = Pd.nth_target (ssph,stm) codim in

        if (Poly.(<>) (ctm,ssph') (tcat,tsph)) then
          Error "Invalid target type"
        else

          let* (fcat,fsph) = Result.of_option (match_cat_type fty)
              ~error:"Filling cell does not have category type." in

          let tlbl = f tnm tict dpth lvl ssph' in
          let (lsph,ltm) = map_disc (ssph',stm') ~f:(lift 1) in
          let ttm = var (lvl+1) lvl tnm in

          let fsph' = Ext (lsph,(ltm,ttm)) in

          if (Poly.(<>) (lift 1 ctm,fsph') (fcat,fsph)) then

            Error "Invalid filling type"

          else

            let ftm = var (lvl+2) (lvl+1) fnm in
            let lfsph = map_sph fsph' ~f:(lift 1) in
            let flbl = f fnm fict dpth (lvl+1) fsph' in
            let* pd' = Pd.insert_right pd tdim tlbl (Pd.Br (flbl,Emp)) in
            Ok (pd', lift 2 ctm, lfsph, ftm, dpth, lvl+2, tdim+1, cnm, cict)

    in let* (pd,_,_,_,_,_,_,cnm,cict) = go 0 tl in Ok ((cnm,cict),pd)

  let fld_dbg (nm : name) (ict : icit) (k : lvl) (l : lvl) (sph : s sph) : unit =
    let pp_ict i = match i with
      | Impl -> "Impl"
      | Expl -> "Expl"
    in Fmt.pr "@[<v>----@,nm : %s@,ict: %s@,k: %d@,l: %d@,sph: @[%a@]@,@]"
      nm (pp_ict ict) k l (pp_sph pp_dbg) sph

  let tele_to_pd (tl : s tele) : ((name * icit) * (name * icit) pd , string) Result.t =
    let f nm ict _ _ _ = (nm,ict) in
    tele_to_pd_fold tl f

  let tele_to_name_pd (tl : s tele) : (name * (name pd) , string) Result.t =
    let f nm _ _ _ _ = nm in
    Result.bind (tele_to_pd_fold tl f)
      ~f:(fun ((cn,_),pd) -> Ok (cn,pd))

  let tele_to_idx_pd (tl : s tele) : (idx pd,string) Result.t =
    let f _ _ k l _ = lvl_to_idx k l in
    Result.bind (tele_to_pd_fold tl f)
      ~f:(fun (_,pd) -> Ok pd)

  let fresh_pd pd =
    let nm_lvl l = Fmt.str "x%d" l in
    Pd.map_pd_lf_nd_lvl pd
      ~lf:(fun lvl _ -> (nm_lvl lvl,Expl))
      ~nd:(fun lvl _ -> (nm_lvl lvl,Impl))

  let args_pd pd =
    let nm_lvl l = Fmt.str "x%d" l in
    Pd.map_pd_lvls pd 0
      ~f:(fun k l _ _ -> var (k+1) (l+1) (nm_lvl (l+1)))

  let nm_ict_args_pd pd =
    Pd.map_pd_lvls pd 0
      ~f:(fun k l _ (nm,ict) -> (nm, ict, var (k+1) (l+1) nm))

  let pd_nm_ict_args (cn,ci) pd =
    let k = Pd.pd_length pd + 1 in
    Pd.fold_pd_lvls pd ~off:1 (Ext (Emp,(var k 0 cn,ci)))
      ~f:(fun _ l _ (nm,ict) args -> Ext (args,(var k l nm,ict)))

  let pd_ict_canon pd =
    map_pd_lf_nd pd
      ~lf:(fun (nm,_) -> (nm,Expl))
      ~nd:(fun (nm,_) -> (nm,Impl))

  let pd_with_impl pd =
    map_pd_lf_nd pd
      ~lf:(fun x -> (x,Expl))
      ~nd:(fun x -> (x,Impl))

end

(* This is a kind of orphan now.... *)
let pd_args cat pd =
  Pd.fold_pd_lf_nd pd (Ext (Emp,(cat,Impl)))
    ~lf:(fun args arg -> Ext (args,(arg,Expl)))
    ~nd:(fun args arg -> Ext (args,(arg,Impl)))

(*****************************************************************************)
(*                                 Coherences                                *)
(*****************************************************************************)

module type CohSyntax = sig
  include PdSyntax
  val app : s -> s -> icit -> s
  val coh : nm_ict -> nm_ict pd -> s -> s -> s -> s
  val disc_coh : nm_ict -> nm_ict pd -> s
end

module CohUtil(C : CohSyntax) = struct
  include C
  include PdUtil(C)

  let app_args t args =
    fold_left args t
      (fun t' (arg,ict) -> app t' arg ict)

  (* Unbiased composition coherence *)
  let rec ucomp_coh' (cn : nm_ict) (pd : nm_ict pd) (d : int) : s =
    if (is_disc pd) && d = dim_pd pd then
      disc_coh cn pd
    else
      match (match_hom (ucomp_ty' cn pd d)) with
      | None -> failwith "empty sphere in ucomp"
      | Some (ty,src,tgt) ->
         coh cn pd ty src tgt

  (* Unbiased Type *)
  and ucomp_ty' (cn : nm_ict) (pd : nm_ict pd) (d : int) : s =
    let bdry = boundary' (args_pd pd) d in
    let ct' = var (pd_length pd + 1) 0 (fst cn) in
    let sph = map_with_lvl bdry ~f:(fun n (s,t) -> (ucomp_app' ct' s n, ucomp_app' ct' t n)) in
    sph_to_cat ct' sph

  (* Applied unbiased composite *)
  and ucomp_app' : s -> s pd -> int -> s = fun ct pd d ->
    if (is_disc pd) && d = dim_pd pd then
      head (labels pd)
    else
      let uc_coh = ucomp_coh' ("C",Impl) (fresh_pd pd) d in
      app_args uc_coh (pd_args ct pd)

  let ucomp_coh cn pd = ucomp_coh' cn pd (dim_pd pd)
  let ucomp_ty cn pd = ucomp_ty' cn pd (dim_pd pd)
  let ucomp_app cn pd = ucomp_app' cn pd (dim_pd pd)

  let ucomp_with_type' : s -> s pd -> int -> s disc = fun ct pd d ->
    let bdry = boundary' pd d in
    let suite_sph = map_with_lvl bdry
        ~f:(fun n (s,t) -> (ucomp_app' ct s n, ucomp_app' ct t n)) in
    (suite_sph , ucomp_app' ct pd d)

  let ucomp_with_type ct pd = ucomp_with_type' ct pd (dim_pd pd)

  let whisker : s -> s disc -> int -> s disc -> s disc =
    fun ct left i right ->
    let wpd = Base.Result.ok_or_failwith
        (whisk_right (disc_pd left) i right) in
    ucomp_with_type ct wpd

  let str_ucomp (c : string) (pd : string pd) : s =
    ucomp_coh (c,Impl) (pd_with_impl pd)

  let gen_ucomp (pd : 'a pd) : s =
    ucomp_coh ("C",Impl) (fresh_pd pd)

end

(*****************************************************************************)
(*                               Generic Syntax                              *)
(*****************************************************************************)

module type Syntax = sig
  include PdSyntax
  include CohSyntax
  val arr : s -> s
  val lam : name -> icit -> s -> s
  val pi : name -> icit -> s -> s -> s
  val pp_s : s Fmt.t
end

module SyntaxUtil(Syn : Syntax) = struct
  include Syn
  include PdUtil(Syn)

  (* Utility Routines *)
  (* let app_args t args =
   *   fold_left args t
   *     (fun t' (arg,ict) -> app t' arg ict)  *)

  let id_sub t =
    let k = length t in
    map_with_lvl t ~f:(fun l (nm,ict,_) ->
        (ict, var k l nm))

  let abstract_tele tele tm =
    fold_right tele tm (fun (nm,ict,_) tm'  ->
        lam nm ict tm')

  let abstract_tele_with_type tl ty tm =
    fold_right tl (ty,tm)
      (fun (nm,ict,ty) (ty',tm') ->
        (pi nm ict ty ty', lam nm ict tm'))

end
