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

let base_sph (ct : 'a cyl_typ) : 'a sph = 
  map_suite ct ~f:(fun ((src,_,_),(tgt,_,_)) -> (src,tgt))

let base_disc ((ct,(b,_,_)) : 'a cyl) : 'a disc =
  (base_sph ct,b)
                      
let lid_sph (ct : 'a cyl_typ) : 'a sph =     
  map_suite ct ~f:(fun ((_,src,_),(_,tgt,_)) -> (src,tgt))

let lid_disc ((ct,(_,l,_)) : 'a cyl) : 'a disc =
  (lid_sph ct,l)

let flat ((sph,ct) : 'a susp_cyl_typ) : 'a disc =
  match ct with
  | [] -> failwith "empty on flat"
  | ((sb,sl,sc),_)::_ -> (sph |> (sb,sl) , sc)

let sharp ((sph,ct) : 'a susp_cyl_typ) : 'a disc =
  match ct with
  | [] -> failwith "empty on sharp"
  | (_,(tb,tl,tc))::_ -> (sph |> (tb,tl) , tc)

(* Folding over lists with three parameters. *)
let rec fold3 a b c init f =
  match (a,b,c) with
  | ([],[],[]) -> init
  | (x::a',y::b',z::c') ->
    fold3 a' b' c' (f init x y z) f
  | _ -> failwith "unequal fold3"

module CylinderOps(C : CylinderSyntax) = struct
  
  include CylinderUtil(C)

  (* Anti lifting? *)
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

  (* Lifting *)
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

(***************************************************************************)
(*                           Cylinder Coherences                           *)
(***************************************************************************)

module CylinderCoh(S: Syntax) = struct 
    include S

    module Su = SyntaxUtil(S)
    module Ops = CylinderOps(Su)
        
    let rec cylcoh_susp (cn : nm_ict) (pd : nm_ict pd) (c : s) 
        (bsph : s sph) ((ssph,s) : s disc) ((tsph,t) : s disc) : s susp_cyl =
      
      match (ssph,tsph) with 
      | (Emp,Emp) ->
        let args = Su.pd_nm_ict_args cn pd in 
        let cc = Su.sph_to_cat c bsph in 
        let coh_tm = Su.app_args (coh cn pd cc s t) args in 
        ((bsph, []), (s, t, coh_tm))
    
      | (Ext (ssph',(ss,st)), Ext (tsph',(ts,tt))) ->

        let d = dim_pd pd in
        let cd = length bsph + length ssph in

        let src_pd = if (cd <= d) then
            Su.pd_ict_canon (truncate true (d-1) pd)
          else pd in
        
        let tgt_pd = if (cd <= d) then
            Su.pd_ict_canon (truncate false (d-1) pd)
          else pd in 
        
        let ((_,ct),(sb,sl,sc)) = cylcoh_susp cn src_pd c bsph (ssph',ss) (tsph',ts) in
        let ((_,_ ),(tb,tl,tc)) = cylcoh_susp cn tgt_pd c bsph (ssph',st) (tsph',tt) in

        (* Super yucky inefficient. *)
        let ct' = List.append ct [(sb,sl,sc),(tb,tl,tc)] in
        let ((coh_sph,_),b,l) = Ops.iter_advance c (bsph,ct') s t (List.length ct') in
        let cc = Su.sph_to_cat c coh_sph in 
        let coh_tm = Su.app_args (coh cn pd cc b l) (Su.pd_nm_ict_args cn pd) in 

        ((bsph,ct'),(s,t,coh_tm))

      | _ -> failwith "cylcoh dimension error"

    
    let cylcoh cn pd c s t =
      let (bc, sph) = Ops.match_homs c in
      let (_,(b,l,cr)) = cylcoh_susp cn pd bc sph s t in
      let result = cyl b l cr  in
      (* Fmt.pr "@[<v>generated cylcoh: @[%a@]@,@]" pp result; *)
      result    
    
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


              



