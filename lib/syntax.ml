(*****************************************************************************)
(*                                                                           *)
(*                        Generic Syntax Constructions                       *)
(*                                                                           *)
(*****************************************************************************)

open Suite
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

type icit =
  | Impl
  | Expl

type 'a tele = (name * icit * 'a) suite

type 'a pd_desc =
  | TelePd of 'a tele
  | TreePd of 'a * 'a pd 

type ucmp_desc =
  | UnitPd of unit pd
  | DimSeq of int list

let pp_ucmp_desc ppf uc =
  let open Fmt in 
  match uc with
  | UnitPd pd -> pf ppf "%a" pp_tr pd
  | DimSeq ds -> pf ppf "%a" (list int) ds 

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
(*                           Generic Syntax Module                           *)
(*****************************************************************************)

module type CatSyntax = sig

  type s

  val obj : s -> s
  val hom : s -> s -> s -> s
  
end

module type Syntax = sig

  include CatSyntax
  
  val lift : int -> s -> s
  val cat : s
  val var : lvl -> lvl -> s
  val lam : name -> icit -> s -> s
  val pi : name -> icit -> s -> s -> s 
  val app : s -> s -> icit -> s

  val coh : s tele -> s -> s -> s -> s
  
  val fresh_cat : lvl -> string * s
  val nm_of : lvl -> s -> string 
  val pp : s Fmt.t
  
end

(*****************************************************************************)
(*                     Semantic Category Implementations                     *)
(*****************************************************************************)

module type CatImpl = sig
  include CatSyntax
  val ucomp : s -> s pd -> s
end

module CatUtils(C: CatImpl) = struct

  include C

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

  let rec sph_to_typ : s -> s sph -> s = fun c sph ->
    match sph with
    | Emp -> c
    | Ext (sph',(s,t)) ->
      hom (sph_to_typ c sph') s t 
  
end

(*****************************************************************************)
(*                              Utility Routines                             *)
(*****************************************************************************)

let pd_args cat pd =
  let open Pd in
  
  let rec pd_args_br args br =
    match br with
    | Br (v,brs) ->
      let ict = if (is_empty brs) then Expl else Impl in
      pd_args_brs (Ext (args,(ict,v))) brs

  and pd_args_brs args brs =
    match brs with
    | Emp -> args
    | Ext (brs',(v,br)) ->
      let args' = pd_args_brs args brs' in
      pd_args_br (Ext (args',(Impl,v))) br 

  in pd_args_br (Ext (Emp,(Impl,cat))) pd 

module SyntaxUtil(Syn : Syntax) = struct
  open Syn

  (* Utility Routines *)
  
  let app_args t args =
    fold_left (fun t' (ict,arg) ->
        app t' arg ict) t args 

  let abstract_tele tele tm =
    fold_right (fun (nm,ict,_) tm'  ->
        lam nm ict tm') tele tm

  (* This could be better if we had a "var" map ... *)
  let fresh_pd pd =
    let k = length (labels pd) in
    pd_lvl_map pd (fun _ l -> var k l)

  (* There is a another version where the sphere is a list ... *)
  let suite_sph_typ bdy ct =
    fold_left (fun ct' (s,t) ->
        hom ct' s t) ct bdy 

    (* Yeah, the inefficiency here is annoying.  
       Surely this can be improved ... *)
  let pd_to_tele pd =
    let k = length (labels pd) in 
    let (cn,ct) = fresh_cat k in 
    let f sph flr tele is_lf =
      let l = length tele in 
      let ict = if is_lf then Expl else Impl in
      let ty = obj (suite_sph_typ sph ct) in
      Ext (tele,(nm_of l flr,ict,lift (l - k - 1) ty))
    in fold_left_with_sph pd f (Ext (Emp,(cn,Impl,cat)))

  (* Unbiased composition coherence *)
  let rec ucomp_coh : type a. a pd -> s = fun pd ->
    if (is_disc pd) then
      let fpd = fresh_pd pd in 
      let tele = pd_to_tele fpd in
      let tm = head (labels fpd) in
      abstract_tele tele tm
    else
      let fpd = fresh_pd pd in
      let tele = pd_to_tele fpd in
      let (_,ct) = fresh_cat (length tele - 1) in 
      let bdry = boundary fpd in
      let sph = map_suite bdry
          ~f:(fun (s,t) -> (ucomp ct s, ucomp ct t)) in
      match sph with
      | Emp -> raise (Failure "empty sphere in ucomp")
      | Ext (sph',(src,tgt)) ->
        coh tele (suite_sph_typ sph' ct) src tgt

  (* Applied unbiased composite *)
  and ucomp : s -> s pd -> s = fun ct pd -> 
    if (is_disc pd) then
      head (labels pd)
    else
      let coh = ucomp_coh pd in
      app_args coh (pd_args ct pd)

  
  include CatUtils(
    struct
      type s = Syn.s
      let ucomp = ucomp
      let obj = Syn.obj
      let hom = Syn.hom 
    end)
      
end

