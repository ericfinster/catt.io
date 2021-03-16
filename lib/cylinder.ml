(*****************************************************************************)
(*                                                                           *)
(*                             Cylinder Routines                             *)
(*                                                                           *)
(*****************************************************************************)

open Base
    
open Pd
open Suite
open Term
open Expr
open Value
open Eval
open Syntax

(* Monadic bind for errors in scope *)
let (let*) m f = Base.Result.bind m ~f 

let rec base_type cat =
  match cat with
  | ArrV c -> Ok c
  | HomV (cat',s,t) ->
    let* bc = base_type cat' in
    Ok (HomV (bc, baseV s, baseV t))
  | _ -> Error `InternalError

let rec lid_type cat =
  match cat with 
  | ArrV c -> Ok c
  | HomV (cat',s,t) ->
    let* bc = lid_type cat' in
    Ok (HomV (bc, lidV s, lidV t))
  | _ -> Error `InternalError

let rec split_cylinder cat = 
  match cat with
  | ArrV c -> Ok (c , Emp, Emp)
  | HomV (c,s,t) ->
    let* (bc,scyl,tcyl) = split_cylinder c in
    let scyl' = Ext (scyl,(baseV s, lidV s, coreV s)) in
    let tcyl' = Ext (tcyl,(baseV t, lidV t, coreV t)) in 
    Ok (bc, scyl', tcyl')
  | _ -> Error `InternalError

(* Some generic routines *)

type 'a blc = 'a * 'a * 'a
type 'a cyl_typ = ('a blc * 'a blc) suite
type 'a cyl = 'a cyl_typ * 'a blc

module CylinderTyping(Cmp: Composable) = struct
  open Cmp
  open CompUtils(Cmp)
  
  let base_sph : s cyl_typ -> s sph =
    fun ct -> map_suite ct
        ~f:(fun ((src,_,_),(tgt,_,_)) -> (src,tgt))

  let lid_sph : s cyl_typ -> s sph =     
    fun ct -> map_suite ct
        ~f:(fun ((_,src,_),(_,tgt,_)) -> (src,tgt))
  
  let rec with_boundaries : s -> s cyl_typ -> (s disc) cyl_typ =
    fun bc ct ->
    match ct with
    | Emp -> Emp
    | Ext (ct',((sb,sl,sc),(tb,tl,tc))) ->
      let cbdrys = with_boundaries bc ct' in
      let src_cores = map_suite cbdrys ~f:(fun ((_,_,cr),_) -> cr) in
      let tgt_cores = map_suite cbdrys ~f:(fun (_,(_,_,cr)) -> cr) in
      let idxd_src_cores = zip_with_idx src_cores in 
      let idxd_tgt_cores = zip_with_idx tgt_cores in 

      let src_base = (base_sph ct',sb) in 
      let src_lid = (lid_sph ct',sl) in
      let tgt_base = (base_sph ct',tb) in
      let tgt_lid = (lid_sph ct',tl) in 


      
      let (sc_sph, sc_source) = fold_left
        (fun dsc (i,cdsc) -> Result.ok_or_failwith (whisker bc dsc i cdsc))
        src_base idxd_tgt_cores in
      
      let (_, sc_target) = fold_left
        (fun dsc (i,cdsc) -> Result.ok_or_failwith (whisker bc cdsc i dsc))
        src_lid idxd_src_cores in 

      let sc_final = (Ext (sc_sph,(sc_source,sc_target)), sc) in 


      
      let (tc_sph, tc_source) = fold_left
        (fun dsc (i,sdsc) -> Result.ok_or_failwith (whisker bc dsc i sdsc))
        tgt_base idxd_tgt_cores in

      let (_, tc_target) = fold_left
        (fun dsc (i,sdsc) -> Result.ok_or_failwith (whisker bc sdsc i dsc))
        tgt_lid idxd_src_cores in

      let tc_final = (Ext (tc_sph,(tc_source,tc_target)), tc) in


      
      Ext (cbdrys,((src_base,src_lid,sc_final),(tgt_base,tgt_lid,tc_final)))
      
end


(*****************************************************************************)
(*                                  Testing                                  *)
(*****************************************************************************)

module ExprComposable = struct
  type s = expr
  let ucomp c pd =
    if (is_disc pd) then
      head (labels pd)
    else
      ExprUtil.app_args (QuotE (PComp (Pd.blank pd)))
        (pd_args c pd)
end

module ExprComp = CompUtils(ExprComposable)
module ExprCyl = CylinderTyping(ExprComposable)


(* Cylinder Tests *)

let mk_cylinder ct =
  map_suite ct
    ~f:(fun ((sb,sl,sc),(tb,tl,tc)) ->
        ((VarE sb, VarE sl, VarE sc),
         (VarE tb, VarE tl, VarE tc)))

let cyl1 = Emp
           |> (("xb", "xl", "xc"),("yb", "yl", "yc"))

let cyl2 = cyl1
           |> (("fb", "fl", "fc"),("gb", "gl", "gc"))

let cyl3 = cyl2
           |> (("ab", "al", "ac"),("bb", "bl", "bc"))

(* Whisker 3 1 2 *)

let left312 = (Emp
               |> (VarE "x", VarE "y")
               |> (VarE "f", VarE "g")
               |> (VarE "a", VarE "b"),
               VarE "m")

let right312 = (Emp
                |> (VarE "x", VarE "y")
                |> (VarE "g", VarE "h"),
                VarE "c")

let cat312 = VarT 9
let fourcell312 = ([(VarT 8, VarT 7);(VarT 6, VarT 5);(VarT 4, VarT 3)], VarT 2)
let twocell312 =  ([(VarT 8, VarT 7);(VarT 6, VarT 1)], VarT 0)

(* Whisker 2 0 2 *)

let cat202 = VarT 9
let left202 = ([(VarT 8, VarT 7);(VarT 6, VarT 5)], VarT 4)
let right202 = ([(VarT 7, VarT 3);(VarT 2, VarT 1)], VarT 0)


              



