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

type icit =
  | Impl
  | Expl

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

  val pp : s Fmt.t
  
end

module PdConversion(P : PdSyntax) = struct
  include P

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

  (* let pd_extend_tele (tl : s tele) ((cnm,cict,ctm) : s decl) (pd : (s decl) pd) : s tele =
   * 
   *   let l = length tl in 
   *   (\* Note: ctm is valid in l + 1 *\)
   *   
   *   let rec do_br sph br tl lvl =
   *     match br with
   *     | Br ((snm,_,src),brs) ->
   *       let ict = if (is_empty brs) then Expl else Impl in
   *       let bc = lift (lvl - l - 1) ctm in 
   *       let sty = obj (sph_to_cat bc sph) in
   *       let tl' =  Ext (tl,(snm,ict,sty)) in
   *       do_brs (map_sph sph ~f:(lift 1)) src brs tl' (lvl+1)
   * 
   *   and do_brs sph src brs tl lvl =
   *     match brs with
   *     | Emp -> (tl, lvl, src)
   *     | Ext (brs',((tnm,_,tgt),br)) ->
   *       let (tl',lvl',src') = do_brs sph src brs' tl lvl in
   *       let bc = lift (lvl'-l-1) ctm in
   *       let sph' = map_sph sph ~f:(lift (lvl' - lvl)) in 
   *       let tty = obj (sph_to_cat bc sph') in
   *       let (tl'',lvl'',_) = do_br
   *           (Ext (map_sph sph' ~f:(lift 1),(lift 1 src',tgt)))
   *           br (Ext (tl',(tnm,Impl,tty))) (lvl'+1) in
   *       (tl'',lvl'',lift (lvl''-lvl'-1) tgt)
   * 
   *   in let (tl,_,_) = do_br Emp pd (Ext (tl,(cnm,cict,cat))) (l+1) in tl
   * 
   * let pd_to_tele (c : s) (pd : (s decl) pd) =
   *   pd_extend_tele Emp ("C",Impl,c) pd *)

  let new_pd_to_tele ((cnm,cict) : (name * icit)) (pd : 'a pd)
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
    new_pd_to_tele c pd (fun _ ni -> ni) (fun _ ni -> ni)

  let string_pd_to_tele (cnm : name) (pd : name pd) : s tele =
    new_pd_to_tele (cnm,Impl) pd (fun _ nm -> (nm,Expl))
      (fun _ nm -> (nm,Impl))
      
  let fresh_pd_tele (pd : 'a pd) : s tele =
    let vn l = Fmt.str "x%d" l in 
    new_pd_to_tele ("C",Impl) pd
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
      nm (pp_ict ict) k l (pp_sph pp) sph

  let tele_to_pd (tl : s tele) : ((name * icit) * (name * icit) pd , string) Result.t =
    let f nm ict _ _ _ = (nm,ict) in 
    tele_to_pd_fold tl f
      
  let tele_to_idx_pd (tl : s tele) : (idx pd,string) Result.t =
    let f _ _ k l _ = lvl_to_idx k l in
    Result.bind (tele_to_pd_fold tl f)
      ~f:(fun (_,pd) -> Ok pd)

  
  (* DEPRECATED *)
  (* let tele_to_pd (depth : int) (tl : s tele) : (s pd, string) Result.t =
   *   let (let*\) m f = Base.Result.bind m ~f in
   *   
   *   let rec go (depth : int) (tl : s tele) = 
   *     match tl with 
   *     | Emp -> Error "Empty context is not a pasting diagram"
   *     | Ext(Emp,_) -> Error "Singleton context is not a pasting diagram"
   * 
   *     | Ext(Ext(tl',(cnm,_,cty)),(onm,_,oty)) when depth = 2 ->
   * 
   *       (\* Fmt.pr "@[<v>cat_tm: %a@,@]" pp cty;
   *        * Fmt.pr "@[<v>cat: %a@,@]" pp cat;
   *        * Fmt.pr "@[<v>obj_tm: %a@,@]" pp oty; *\)
   *       let l = length tl' in
   *       let cvar = var (l+1) l cnm in
   *       (\* Fmt.pr "@[<v>obj cvar: %a@,@]" pp (obj cvar); *\)
   *       let svar = var (l+2) (l+1) onm in 
   *       if (Poly.(<>) cty cat) then
   *         Error "Pasting diagram does not start with an abstract category"
   *       else if (Poly.(<>) oty (obj cvar)) then
   *         Error "Initial object not in the correct category"
   *       else Ok (Pd.Br (svar,Emp), lift 1 cvar , Emp, svar, l+2, l)
   * 
   *     | Ext(Ext(tl',(tnm,_,tty)),(fnm,_,fty)) ->
   * 
   *       let* (pd,ctm,ssph,stm,lvl,dim) = go (depth - 2) tl' in
   * 
   *       let* (tcat,tsph) = Result.of_option (match_cat_type tty)
   *           ~error:"Target cell does not have category type." in
   * 
   *       let tdim = length tsph in 
   *       let codim = dim - tdim in
   *       let (ssph',stm') = Pd.nth_target (ssph,stm) codim in 
   * 
   *       (\* Fmt.pr "@[<v>Expected target cat: %a@,Received target cat: %a@,@]"
   *        *   pp ctm pp tcat;
   *        * Fmt.pr "@[<v>Expected target sphere: %a@,Received target sphere: %a@,@]"
   *        *   (pp_sph pp) ssph' (pp_sph pp) tsph; *\)
   * 
   *       if (Poly.(<>) (ctm,ssph') (tcat,tsph)) then
   *         Error "Invalid target type"
   *       else
   * 
   *         let* (fcat,fsph) = Result.of_option (match_cat_type fty)
   *             ~error:"Filling cell does not have category type." in
   * 
   *         let (lsph,ltm) = map_disc (ssph',stm') ~f:(lift 1) in 
   *         let ttm = var (lvl+1) lvl tnm in
   *         let fsph' = Ext (lsph,(ltm, ttm)) in
   * 
   *         if (Poly.(<>) (lift 1 ctm,fsph') (fcat,fsph)) then
   * 
   *           let _ = 5 in
   *           
   *           (\* Fmt.pr "@[<v>Expected filling cat: %a@,Received filling cat: %a@,@]"
   *            *   pp ctm pp fcat;
   *            * Fmt.pr "@[<v>Expected filling sphere: %a@,Received filling sphere: %a@,@]"
   *            *   (pp_sph pp) fsph' (pp_sph pp) fsph; *\)
   * 
   *           Error "Invalid filling type"
   * 
   *         else
   * 
   *           let ftm = var (lvl+2) (lvl+1) fnm in
   *           let lfsph = map_sph fsph' ~f:(lift 1) in 
   *           let* pd' = Pd.insert_right pd tdim ttm (Pd.Br (ftm,Emp)) in
   *           Ok (pd', lift 2 ctm, lfsph, ftm, lvl+2, tdim+1)
   * 
   *   in let* (pd,_,_,_,_,_) = go depth tl in Ok pd *)

  let fresh_pd pd =
    let nm_lvl l = Fmt.str "x%d" l in 
    Pd.map_pd_lf_nd_lvl pd
      ~lf:(fun lvl _ -> (nm_lvl lvl,Expl))
      ~nd:(fun lvl _ -> (nm_lvl lvl,Impl))

  let args_pd pd =
    let nm_lvl l = Fmt.str "x%d" l in
    Pd.map_pd_lvls pd 0
      ~f:(fun k l _ _ -> var (k+1) (l+1) (nm_lvl (l+1)))
      
end

let pd_args cat pd =
  Pd.fold_pd_lf_nd pd (Ext (Emp,(Impl,cat)))
    ~lf:(fun args arg -> Ext (args,(Expl,arg)))
    ~nd:(fun args arg -> Ext (args,(Impl,arg)))

(*****************************************************************************)
(*                              Cylinder Syntax                              *)
(*****************************************************************************)

module type CylinderSyntax = sig
  include PdSyntax
  val ucomp : s -> s pd -> s
end

module CylinderUtil(C: CylinderSyntax) = struct

  include C
  include PdConversion(C)
  
  let ucomp_with_type : s -> s pd -> s disc = fun ct pd -> 
    let bdry = boundary pd in
    let suite_sph = map_suite bdry
        ~f:(fun (s,t) -> (ucomp ct s, ucomp ct t)) in
    (suite_sph , ucomp ct pd)

  let whisker : s -> s disc -> int -> s disc -> s disc =
    fun ct left i right ->
    let wpd = Base.Result.ok_or_failwith
        (whisk_right (disc_pd left) i right) in 
    ucomp_with_type ct wpd
  
end

(*****************************************************************************)
(*                               Generic Syntax                              *)
(*****************************************************************************)
    
module type Syntax = sig
  include PdSyntax
  val lam : name -> icit -> s -> s
  val pi : name -> icit -> s -> s -> s 
  val app : s -> s -> icit -> s
  val coh : (name * icit) -> (name * icit) pd -> s -> s -> s -> s
  val cyl : s -> s -> s -> s
end

module SyntaxUtil(Syn : Syntax) = struct
  include Syn
  include PdConversion(Syn)

  (* Utility Routines *)
  let app_args t args =
    fold_left (fun t' (ict,arg) ->
        app t' arg ict) t args 

  let id_sub t =
    let k = length t in
    map_with_lvl t ~f:(fun l (nm,ict,_) ->
        (ict, var k l nm))
          
  let abstract_tele tele tm =
    fold_right (fun (nm,ict,_) tm'  ->
        lam nm ict tm') tele tm

  let abstract_tele_with_type tl ty tm =
    fold_right (fun (nm,ict,ty) (ty',tm') ->
        (pi nm ict ty ty', lam nm ict tm'))
      tl (ty,tm)
  
  (* Unbiased composition coherence *)
  (* FIXME! Needs debug! *)
  let rec ucomp_coh : type a. a pd -> s = fun pd ->
    if (is_disc pd) then
      let tele = fresh_pd_tele pd in 
      let lvl = length tele in 
      abstract_tele tele
        (var (lvl+1) lvl (Fmt.str "x%d" lvl))
    else
      let fpd = fresh_pd pd in
      let bdry = boundary (args_pd pd) in
      (* INEFFICIENT: make a pd counting function ... *)
      let ct' = var (length (labels fpd)) 0 "C" in
      let sph = map_suite bdry
          ~f:(fun (s,t) -> (ucomp ct' s, ucomp ct' t)) in
      match sph with
      | Emp -> failwith "empty sphere in ucomp"
      | Ext (sph',(src,tgt)) ->
        coh ("C",Impl) fpd (sph_to_cat ct' sph') src tgt
  
  (* Applied unbiased composite *)
  and ucomp : s -> s pd -> s = fun ct pd -> 
    if (is_disc pd) then
      head (labels pd)
    else
      let coh = ucomp_coh pd in
      app_args coh (pd_args ct pd)

  let ucomp_with_type : s -> s pd -> s disc = fun ct pd -> 
    let bdry = boundary pd in
    let suite_sph = map_suite bdry
        ~f:(fun (s,t) -> (ucomp ct s, ucomp ct t)) in
    (suite_sph , ucomp ct pd)

  let whisker : s -> s disc -> int -> s disc -> s disc =
    fun ct left i right ->
    let wpd = Base.Result.ok_or_failwith
        (whisk_right (disc_pd left) i right) in 
    ucomp_with_type ct wpd

end

