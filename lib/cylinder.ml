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
open Syntax

(* Monadic bind for errors in scope *)
let (let*) m f = Base.Result.bind m ~f

(* Some generic routines *)

type 'a blc = 'a * 'a * 'a
type 'a cyl_typ = ('a blc * 'a blc) suite
type 'a cyl = 'a cyl_typ * 'a blc

type 'a susp_cyl_typ = 'a sph * ('a blc * 'a blc) list
type 'a susp_cyl = 'a susp_cyl_typ * 'a blc

let pp_blc pp_el ppf (b,l,c) = 
  Fmt.pf ppf "(@[%a@]@;,@[%a@]@;,@[%a@])"
    pp_el b pp_el l pp_el c
    
let pp_susp_cyl_typ pp_el ppf (bsph,ct) =
  Fmt.pf ppf "@[<hov> @[%a@]@]@;| @[<hov>%a@]"
    (pp_sph pp_el) bsph
    (Fmt.list (Fmt.pair ~sep:(Fmt.any " => ")
                 (pp_blc pp_el) (pp_blc pp_el))) ct

let base_sph (ct : 'a cyl_typ) : 'a sph =
  map_suite ct ~f:(fun ((src,_,_),(tgt,_,_)) -> (src,tgt))

let base_disc ((ct,(b,_,_)) : 'a cyl) : 'a disc =
  (base_sph ct,b)

let susp_base_sph (ct : 'a susp_cyl_typ) : 'a sph =
  Suite.append_list (fst ct)
    (List.map (snd ct)
       ~f:(fun ((src,_,_),(tgt,_,_)) -> (src,tgt)))

let lid_sph (ct : 'a cyl_typ) : 'a sph =
  map_suite ct ~f:(fun ((_,src,_),(_,tgt,_)) -> (src,tgt))

let lid_disc ((ct,(_,l,_)) : 'a cyl) : 'a disc =
  (lid_sph ct,l)

let susp_lid_sph (ct : 'a susp_cyl_typ) : 'a sph =
  Suite.append_list (fst ct)
    (List.map (snd ct)
       ~f:(fun ((_,src,_),(_,tgt,_)) -> (src,tgt)))

let flat ((sph,ct) : 'a susp_cyl_typ) : 'a disc =
  match ct with
  | [] -> failwith "empty on flat"
  | ((sb,sl,sc),_)::_ -> (sph |> (sb,sl) , sc)

let sharp ((sph,ct) : 'a susp_cyl_typ) : 'a disc =
  match ct with
  | [] -> failwith "empty on sharp"
  | (_,(tb,tl,tc))::_ -> (sph |> (tb,tl) , tc)

let map_cyl_bdry (b : ('a blc * 'a blc) list) ~f:(f : 'a -> 'b) =
  let f' ((sb,sl,sc),(tb,tl,tc)) =
    ((f sb, f sl, f sc), (f tb, f tl, f tc)) in 
  List.map b ~f:f'
  
(* Folding over lists with three parameters. *)
let rec fold3 a b c init f =
  match (a,b,c) with
  | ([],[],[]) -> init
  | (x::a',y::b',z::c') ->
    fold3 a' b' c' (f init x y z) f
  | _ -> failwith "unequal fold3"

module CylinderOps(C : CylinderSyntax) = struct

  include C
  include PdUtil(C)
  open CohUtil(C)

  (* convert a cylinder type to a semantic type *)
  let cyl_to_cat (bc : s) ((sph,ct) : s susp_cyl_typ) : s =
    let arr_cat = arr (sph_to_cat bc sph) in
    List.fold ct ~init:arr_cat
      ~f:(fun c ((sb,sl,sc),(tb,tl,tc)) ->
          hom c (cyl sb sl sc) (cyl tb tl tc))

  (***************************************************************************)
  (*                           Underlying Cylinders                          *)
  (***************************************************************************)

  let advance (bc : s) ((sph,ct) : s susp_cyl_typ) (b : s) (l : s)
    : s susp_cyl_typ * s disc * s disc * s * s * s * s =

    match ct with
    | [] -> failwith "advance on empty cylinder context"
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

      ((sph' , to_list cts) , (bsph,b) , (lsph,l) , sc , tc , b' , l')

  let rec iter_advance (bc : s) (sct : s susp_cyl_typ) (b : s) (l : s) (n : int)
    : s susp_cyl_typ * s * s =
    if (n <= 0) then (sct,b,l) else
      let (sct',_,_,_,_,b',l') = advance bc sct b l in
      iter_advance bc sct' b' l' (n-1)

  let core_sph (bc : s) (sct : s susp_cyl_typ) (b : s) (l : s) : s sph =
    let n = List.length (snd sct) in
    let ((sph,_),b',l') = iter_advance bc sct b l n in
    sph |> (b',l')

  let underlying_data (bc : s) ((sct,(b,l,c)) : s susp_cyl)
    : s susp_cyl * s disc * s disc * s * s =
    let (ct,bdisc,ldisc,sc,tc,b',l') = advance bc sct b l in
    ((ct,(b',l',c)),bdisc,ldisc,sc,tc)

  let underlying_cyl (bc : s) (sc : s susp_cyl) : s susp_cyl =
    let (cyl,_,_,_,_) = underlying_data bc sc in cyl

  let rec nth_underlying (bc : s) (sc : s susp_cyl) (n : int) : s susp_cyl =
    if (n <= 0) then sc else
      nth_underlying bc (underlying_cyl bc sc) (n-1)


  (***************************************************************************)
  (*                                 Lifting                                 *)
  (***************************************************************************)

  let lift (((sph,ct),(_,_,c)) : s susp_cyl)
      ((bsph,b) : s disc) ((lsph,l) : s disc)
      (sc : s) (tc : s) : s susp_cyl =

    match sph with
    | Emp -> failwith "lift on unsuspended cylinder"
    | Ext (sph',(sb,tl)) ->

      let i = length sph in

      let (tb,brem) =
        (match snd (split_at (i-1) bsph) with
         | ((_,tb)::brem) -> (tb,brem)
         | _ -> failwith "dimension error in base") in

      let (sl,lrem) =
        (match snd (split_at (i-1) lsph) with
         | ((sl,_)::lrem) -> (sl,lrem)
         | _ -> failwith "dimension error in lid") in

      let go_fold ct (sb,tb) (sl,tl) ((_,_,sc),(_,_,tc))  =
        ct |> ((sb,sl,sc),(tb,tl,tc)) in

      let cts = fold3 brem lrem ct Emp go_fold in
      let ct' = to_list cts in

      ((sph',((sb,sl,sc),(tb,tl,tc))::ct'),(b,l,c))

  let lift_curried (scyl,bd,ld,sc,tc) =
    lift scyl bd ld sc tc

end

module CylinderCoh(Syn: Syntax) = struct

  include PdUtil(Syn)
  open CohUtil(Syn)
  open SyntaxUtil(Syn)
  open CylinderOps(Syn)

  (***************************************************************************)
  (*                           Cylinder Coherences                           *)
  (***************************************************************************)

  let cylcoh_susp (cn : nm_ict) (pd : nm_ict pd) (c : s)
      (bsph : s sph) ((ssph,s) : s disc) ((tsph,t) : s disc) : s susp_cyl =

    (* log_msg "in cylcoh_susp"; *)

    let args = nm_ict_args_pd pd in
    let bdim = length bsph in
    
    (* log_val "args" (ext_args args)
     *   (pp_suite
     *      (fun ppf (arg,ict) ->
     *         Fmt.pf ppf "(%a,%a)" pp_s arg pp_ict ict)); *)
    
    (* log_val "bsph" bsph (pp_sph pp_s);
     * 
     * log_val "s" s pp_s;
     * log_val "t" t pp_s; *)
    
    let go_fold (ct,k) ((ss,st),(ts,tt)) =

      let ext_args arg_pd =
        fold_pd_lf_nd arg_pd (Ext (Emp,(c,Impl)))
          ~lf:(fun args (_,_,arg) -> Ext (args,(arg,Expl)))
          ~nd:(fun args (_,_,arg) -> Ext (args,(arg,Impl))) in 
      
      (* let lg s x p = log_val ~idt:(k*2) s x p in *)
      let tdim = bdim + k in

      (* lg "ss" ss pp_s;
       * lg "st" st pp_s;
       * lg "ts" ts pp_s;
       * lg "tt" tt pp_s; *)
      
      let src_sub = strengthen true tdim pd in 
      let tgt_sub = strengthen false tdim pd in
      let str_bsph = map_suite bsph
          ~f:(fun (s,t) -> (src_sub s, tgt_sub t)) in
      
      let src_ct = map_cyl_bdry ct ~f:src_sub in
      let ss' = src_sub ss in
      let ts' = src_sub ts in
      let src_c = src_sub c in
      let ((src_cc,_),sb,sl) = iter_advance src_c (str_bsph , src_ct) ss' ts' k in
      let src_pd = pd_ict_canon (truncate true tdim pd) in
      let sc_coh = coh cn src_pd (sph_to_cat src_c src_cc) sb sl in
      let sc_args = ext_args (truncate true tdim args) in

      (* lg "sc_coh" sc_coh pp_s;
       * lg "sc_args" sc_args
       *   (pp_suite (fun ppf (a,ict) -> 
       *        match ict with
       *        | Impl -> Fmt.pf ppf "{%a}" pp_s a
       *        | Expl -> Fmt.pf ppf "%a" pp_s a 
       *      )); *)
        
      let sc = app_args sc_coh sc_args in 

      let tgt_ct = map_cyl_bdry ct ~f:tgt_sub in
      let st' = tgt_sub st in
      let tt' = tgt_sub tt in 
      let tgt_c = tgt_sub c in 
      let ((tgt_cc,_),tb,tl) = iter_advance tgt_c (str_bsph , tgt_ct) st' tt' k in 
      let tgt_pd = pd_ict_canon (truncate false tdim pd) in
      let tc_coh = coh cn tgt_pd (sph_to_cat tgt_c tgt_cc) tb tl in
      let tc_args = ext_args (truncate false tdim args) in

      (* lg "tc_coh" tc_coh pp_s;
       * lg "tc_args" tc_args
       *   (pp_suite (fun ppf (a,ict) -> 
       *        match ict with
       *        | Impl -> Fmt.pf ppf "{%a}" pp_s a
       *        | Expl -> Fmt.pf ppf "%a" pp_s a 
       *      )); *)
      
      let tc = app_args tc_coh tc_args in 
      
      (List.append ct [((ss,ts,sc),(st,tt,tc))], k+1)
  
    in
    
    let lst = match List.zip (to_list ssph) (to_list tsph) with
      | Ok l -> l
      | _ -> failwith "unequal sphere dimensions" in
    
    let (ct,k) = List.fold lst ~init:([], 0) ~f:go_fold in

    let ((top_cc,_),b,l) = iter_advance c (bsph , ct) s t k in
    let top_coh = coh cn pd (sph_to_cat c top_cc) b l in
    let top_args = pd_nm_ict_args cn pd in 
    let top = app_args top_coh top_args in 
    
    ((bsph,ct),(s,t,top))

  let cylcoh_impl cn pd c s t =
    let (bc, sph) = match_homs c in
    let (ct,(b,l,cr)) = cylcoh_susp cn pd bc sph s t in
    (* log_val "ct" ct (pp_susp_cyl_typ pp_s);
     * log_val "b" b pp_s;
     * log_val "l" l pp_s;
     * log_val "cr" cr pp_s; *)
    let cyl_typ = cyl_to_cat bc ct in
    let g = nm_ict_pd_to_tele cn pd in
    abstract_tele_with_type g (obj cyl_typ) (cyl b l cr)

  (* A naive, unfolded calculation of the type *)
  let cyl_coh_typ cn pd ct ssph tsph =
    fst (cylcoh_impl cn pd ct ssph tsph)

end

(*****************************************************************************)
(*                   Expr and Term Cylinder Implementations                  *)
(*****************************************************************************)

module ExprCyl = CylinderOps(ExprUtil)
module ExprCylCoh = CylinderCoh(ExprSyntax)
module TermCyl = CylinderOps(TermUtil)
module TermCylCoh = CylinderCoh(TermSyntax)

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
