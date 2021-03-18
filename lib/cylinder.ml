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


(* These guys are somewhat abandoned now.  Make them 
   generic somehow? 
*)
    
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

type 'a susp_cyl_typ = 'a sph * ('a blc * 'a blc) list 
type 'a susp_cyl = 'a susp_cyl_typ * 'a blc

let base_sph (ct : 'a cyl_typ) : 'a sph = 
  map_suite ct ~f:(fun ((src,_,_),(tgt,_,_)) -> (src,tgt))

let base_disc ((ct,(b,_,_)) : 'a cyl) : 'a disc =
  (base_sph ct,b)
                      
let lid_sph (ct : 'a cyl_typ) : 'a sph =     
  map_suite ct ~f:(fun ((_,src,_),(_,tgt,_)) -> (src,tgt))

let lid_disc ((ct,(_,l,_)) : 'a cyl) : 'a disc =
  (lid_sph ct,l)
                      
let core_sph (ct : 'a cyl_typ) : 'a sph =
  map_suite ct ~f:(fun ((_,_,src),(_,_,tgt)) -> (src,tgt))

let rec expose_base (ct : 'a cyl_typ) : ('a blc * 'a blc) * 'a cyl_typ =
  match ct with
  | Emp -> raise (Failure "empty in expose_base")
  | Ext (Emp,x) -> (x,Emp)
  | Ext (ct',x) ->
    let (r,ct'') = expose_base ct' in
    (r, ct'' |> x)

let flat ((sph,ct) : 'a susp_cyl_typ) : 'a disc =
  match ct with
  | [] -> raise (Failure "empty on flat")
  | ((sb,sl,sc),_)::_ -> (sph |> (sb,sl) , sc)

let sharp ((sph,ct) : 'a susp_cyl_typ) : 'a disc =
  match ct with
  | [] -> raise (Failure "empty on flat")
  | (_,(tb,tl,tc))::_ -> (sph |> (tb,tl) , tc)

(* let rec with_types (ct : 'a cyl_typ) : ('a cyl) sph =
 *   match ct with
 *   | Emp ->  Emp
 *   | Ext (ct,(s,t)) ->
 *     with_types ct |> ((ct,s),(ct,t)) *)

(* let rec with_types_susp ((sph,ct) : 'a susp_cyl_typ) : ('a susp_cyl) lsph =
 *   match ct with
 *   | [] -> []
 *   | (l,r)::ct' ->
 *     let r = with_type_susp (sph,ct') in
 *     let f ((sl,cl),(sr,cr)) =
 *       ((sl,()::cl),(sr,()::cr)) in
 *     let h = (sph,
 * 
 * (\* Okay, isn't it just like the "list of prefixes"? *\)
 * let rec prefixes l =
 *   match l with
 *   | [] -> []
 *   | x::xs ->
 *     [x]::(List.map (prefixes xs) ~f:(fun p -> x::p))
 * 
 *     (\* [1,2,3,4] -> [[1],[1,2],[1,2,3],[1,2,3,4]] *\) *)

         
module CylinderTyping(C: CatImpl) = struct
  open CatUtils(C)

  let core_dom_disc (c : s) (susp: int) (base_dsc : s disc)
      (tgt_cores : (s disc) suite) : s disc =
    fold_left (fun dsc (i,cr_dsc) ->
        whisker c dsc (i+susp) cr_dsc)
      base_dsc (zip_with_idx tgt_cores)

  let core_cod_disc (c : s) (susp : int) (lid_dsc : s disc)
      (src_cores : (s disc) suite) : s disc =
    fold_left (fun dsc (i,cr_dsc) ->
        whisker c cr_dsc (i+susp) dsc)
      lid_dsc (zip_with_idx src_cores)  

  (* This is slightly inefficient as we keep zipping and unzipping
     the data.  Perhaps this could be avoided with a more elaborate
     return type? 
  *)
  let rec cyl_typ_discs (bc : s) (sph : s sph) (ct : s cyl_typ) : (s disc) cyl_typ =
    match ct with
    | Emp -> Emp
    | Ext (ct',((sb,sl,sc),(tb,tl,tc))) ->
      
      let cbdrys = cyl_typ_discs bc sph ct' in
      let src_cores = map_suite cbdrys ~f:(fun ((_,_,cr),_) -> cr) in
      let tgt_cores = map_suite cbdrys ~f:(fun (_,(_,_,cr)) -> cr) in
      let shft = length sph in 
      
      (* Calculate the source disc *)
      let src_base_disc = (sph |*> base_sph ct',sb) in 
      let src_lid_disc = (sph |*> lid_sph ct',sl) in
      let (src_sph, src_core_dom) = core_dom_disc bc shft src_base_disc tgt_cores in 
      let (_      , src_core_cod) = core_cod_disc bc shft src_lid_disc src_cores in
      let src_core_disc = (src_sph |> (src_core_dom, src_core_cod) , sc) in 

      (* Calculate the target disc *)
      let tgt_base_disc = (sph |*> base_sph ct',tb) in
      let tgt_lid_disc = (sph |*> lid_sph ct',tl) in 
      let (tgt_sph, tgt_core_dom) = core_dom_disc bc shft tgt_base_disc tgt_cores in
      let (_      , tgt_core_cod) = core_cod_disc bc shft tgt_lid_disc src_cores in 
      let tgt_core_disc = (tgt_sph |> (tgt_core_dom, tgt_core_cod) , tc) in 

      (* Final Result *)
      cbdrys |> ((src_base_disc, src_lid_disc, src_core_disc),
                 (tgt_base_disc, tgt_lid_disc, tgt_core_disc))
  
  let cyl_core_disc (bc : s) (sph : s sph) ((ct,(b,l,c)) : s cyl) : s disc =
    
    let cbdrys = cyl_typ_discs bc sph ct in
    let src_cores = map_suite cbdrys ~f:(fun ((_,_,cr),_) -> cr) in
    let tgt_cores = map_suite cbdrys ~f:(fun (_,(_,_,cr)) -> cr) in
    let shft = length sph in 

    let base_disc = (base_sph ct , b) in
    let lid_disc = (lid_sph ct , l) in 

    let (core_sph, core_dom) = core_dom_disc bc shft base_disc tgt_cores in 
    let (_       , core_cod) = core_cod_disc bc shft lid_disc src_cores in
    (core_sph |> (core_dom, core_cod) , c) 

  (* This version seems to have trouble with the base case ... *)
  (* let rec underlying' : s -> s susp_cyl -> s susp_cyl =
   *   fun bc (sph,ct,(b,l,c)) ->
   * 
   *     let go ((lt,l),(rt,r)) =
   *       let (_,_,lr) = underlying' bc (sph,lt,l) in
   *       let (_,_,rr) = underlying' bc (sph,rt,r) in
   *       (lr,rr)
   *     in
   * 
   *     let ct' = map_suite (with_types ct) ~f:go in 
   * 
   *     let (((sb,sl,sc),(tb,tl,tc)),_) = expose_base ct in
   * 
   *     let i = length sph in
   * 
   *     let sph' = sph |> (sb,tl) in
   *     let sdisc = (sph |> (sb,sl) , sc) in 
   *     let tdisc = (sph |> (tb,tl) , tc) in
   * 
   *     let bdisc = (sph |*> base_sph ct , b) in
   *     let ldisc = (sph |*> lid_sph ct , l) in 
   * 
   *     let bres = snd (whisker bc bdisc i tdisc) in
   *     let lres = snd (whisker bc sdisc i ldisc) in 
   * 
   *     (sph', ct', (bres,lres,c)) *)

  
  let underlying_data (bc : s) (((sph,ct),(b,l,c)) : s susp_cyl)
    : s susp_cyl * s disc * s disc * s * s =
  
    match ct with
    | [] -> raise (Failure "empty cylinder context")
    | ((sb,sl,sc),(tb,tl,tc))::crem -> 
      
      let sph' = sph |> (sb,tl) in
      let sdisc = (sph |> (sb,sl) , sc) in 
      let tdisc = (sph |> (tb,tl) , tc) in
      let i = length sph in

      let go_fold (ct,bsph,lsph) ((sb,sl,sc),(tb,tl,tc)) =

        let sb' = snd (whisker bc (bsph,sb) i tdisc) in 
        let sl' = snd (whisker bc sdisc i (lsph,sl)) in
        let tb' = snd (whisker bc (bsph,tb) i tdisc) in
        let tl' = snd (whisker bc sdisc i (lsph,tl)) in

        (ct   |> ((sb',sl',sc),(tb',tl',tc)),
         bsph |> (sb,tb),
         lsph |> (sl,tl))
        
      in

      let (cts,bsph,lsph) = List.fold crem
          ~init:(Emp, sph |> (sb,tb), sph |> (sl,tl)) ~f:go_fold in 

      let b' = snd (whisker bc (bsph , b) i tdisc) in
      let l' = snd (whisker bc sdisc i (lsph , l)) in 

      (((sph', to_list cts),(b',l',c)) ,
       (bsph , b), (lsph, l), sc, tc)

  
  let underlying_cyl (bc : s) (sc : s susp_cyl) : s susp_cyl = 
    let (cyl,_,_,_,_) = underlying_data bc sc in cyl
      
  
  (* let lift : s -> s susp_cyl -> s disc -> s disc -> s -> s -> s susp_cyl =
   *   fun bc scyl x y umin uplus ->
   * 
   *   
   *   scyl *)

  
  (* let rec lift : 'a susp_cyl -> ('a * 'a * 'a) -> ('a * 'a * 'a) -> 'a susp_cyl =
   *   fun (sph,ctyp,(b,l,c)) uflat usharp -> 
   *   let (((sb,sl,sc),(tb,tl,tc)),cl) = split_at 1 ctyp in
   *   match sph with
   *   | Emp -> raise (Failure "empty sph in lift")
   *   | Ext (sph',(src,tgt)) ->
   *     
   *   (sph', with_list (Emp |> (uflat,usharp) |> ((),())) cl, (b,l,c))
   *   (uflat,usharp) (uflat,usharp) (uflat,usharp) ..... *)

  (* let cyl_whisk : s -> s susp_cyl -> s disc -> s susp_cyl =
   *   fun bcat (sph,scyl_typ,(b,l,c)) cell ->
   *   match scyl_typ with
   *   | Emp ->
   *     let u = (Ext (sph,(b,l)), c) in 
   *     let d = length (fst cell) in 
   *     whisker bcat u (d-1) cell
   *   | Ext (scyl',((sb,sl,sc),(tb,tl,tc))) -> 
   *     
   *     let u0 = sldkfjsdf in
   *     let u1 = lskjsdfaa in
   *     let u2 = alskdfjsdf in
   *     
   *     let ul = cyl_concat u0 u1 u2 in 
   * 
   *     ???? *)
  
end

(*****************************************************************************)
(*                          Category Implementations                         *)
(*****************************************************************************)

module ValueImpl = struct
  type s = value

  let obj c = ObjV c
  let hom c s t = HomV (c,s,t)
  let ucomp c pd =
    if (is_disc pd) then
      head (labels pd)
    else
      let qcmd = PComp (Pd.blank pd) in 
      let qtm = QuotT (qcmd, term_ucomp_coh pd) in
      let qv = eval Emp Emp qtm in 
      appArgs qv (pd_args c pd)

end

module ExprImpl = struct
  
  type s = expr
    
  let obj c = ObjE c
  let hom c s t = HomE (c,s,t)
  let ucomp c pd =
    if (is_disc pd) then
      head (labels pd)
    else
      ExprUtil.app_args (QuotE (PComp (Pd.blank pd)))
        (pd_args c pd)
end

module ExprCyl = CylinderTyping(ExprImpl)
module ValueCyl = CylinderTyping(ValueImpl)

(*****************************************************************************)
(*                                  Testing                                  *)
(*****************************************************************************)


(* Cylinder Tests *)

let mk_susp_cyl_typ sph ct =
  let addVar ((sb,sl,sc),(tb,tl,tc)) =
    ((VarE sb, VarE sl, VarE sc),
     (VarE tb, VarE tl, VarE tc))
  in (sph , List.map (to_list ct) ~f:addVar)

let mk_susp_cyl sph (ct,(b,l,c)) =
  (mk_susp_cyl_typ sph ct,(VarE b, VarE l, VarE c))
       
let cylt1 = Emp   |> (("xb", "xl", "xc"),("yb", "yl", "yc")) 
let cylt2 = cylt1 |> (("fb", "fl", "fc"),("gb", "gl", "gc")) 
let cylt3 = cylt2 |> (("ab", "al", "ac"),("bb", "bl", "bc")) 
let cylt4 = cylt3 |> (("mb", "ml", "mc"),("nb", "nl", "nc")) 

let cyl1 = (cylt1 , ("fb", "fl", "fc"))
let cyl2 = (cylt2 , ("ab", "al", "ac"))
let cyl3 = (cylt3 , ("mb", "ml", "mc"))
let cyl4 = (cylt4 , ("pb", "pl", "pc"))

let pp_blc pp_el ppf (b,l,c) =
  let open Fmt in 
  pf ppf "@[<v>base: %a@,lid:  %a@,core: %a@,@]" pp_el b pp_el l pp_el c
    
let pp_cyl_typ pp_el ppf ct =
  let open Fmt in
  pf ppf "@[<v>%a@]"
    (pp_suite ~sep:cut (pair ~sep:cut (pp_blc pp_el) (pp_blc pp_el)))
    ct
  
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


              



