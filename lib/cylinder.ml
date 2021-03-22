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
  | [] -> raise (Failure "empty on flat")
  | ((sb,sl,sc),_)::_ -> (sph |> (sb,sl) , sc)

let sharp ((sph,ct) : 'a susp_cyl_typ) : 'a disc =
  match ct with
  | [] -> raise (Failure "empty on flat")
  | (_,(tb,tl,tc))::_ -> (sph |> (tb,tl) , tc)

(* Folding over lists with three parameters. *)
let rec fold3 a b c init f =
  match (a,b,c) with
  | ([],[],[]) -> init
  | (x::a',y::b',z::c') ->
    fold3 a' b' c' (f init x y z) f
  | _ -> raise (Failure "unequal fold3")
         
module CylinderOps(C: CatImpl) = struct
  include CatUtils(C)

  (* Anti lifting? *)
  let advance (bc : s) ((sph,ct) : s susp_cyl_typ) (b : s) (l : s)
    : s susp_cyl_typ * s disc * s disc * s * s * s * s = 
    
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
    | Emp -> raise (Failure "lift on unsuspended cylinder")
    | Ext (sph',(sb,tl)) -> 
    
      let i = length sph in

      let (tb,brem) =
        (match snd (split_at (i-1) bsph) with
         | ((_,tb)::brem) -> (tb,brem)
         | _ -> raise (Failure "dimension error in base")) in 

      let (sl,lrem) =
        (match snd (split_at (i-1) lsph) with
         | ((sl,_)::lrem) -> (sl,lrem)
         | _ -> raise (Failure "dimension error in lid")) in 
      
      let go_fold ct (sb,tb) (sl,tl) ((_,_,sc),(_,_,tc))  =
        ct |> ((sb,sl,sc),(tb,tl,tc)) in 

      let cts = fold3 brem lrem ct Emp go_fold in 
      let ct' = to_list cts in 
      
      ((sph',((sb,sl,sc),(tb,tl,tc))::ct'),(b,l,c))

  let lift_curried (scyl,bd,ld,sc,tc) =
    lift scyl bd ld sc tc
  
end


(* module CoherenceCylinders(Syn: Syntax) = struct
 *   open Syn
 *   open SyntaxUtil(Syn) 
 * 
 *   
 *   (\* Coherence cylinders *\)
 *   let coh_cyl : type a. a pd -> s sph -> s disc -> s disc -> s susp_cyl =
 *     fun _ sph (usph,u) (vsph,v) ->
 * 
 *     match (usph,vsph) with
 *     | (Emp,Emp) -> ((sph,[]),(u,u,v))
 *     | _ -> ((sph,[]),(u,u,v))
 * 
 *   
 * end *)


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

module ExprCyl = CylinderOps(ExprImpl)
module ValueCyl = CylinderOps(ValueImpl)

(*****************************************************************************)
(*                          Value Matching Routines                          *)
(*****************************************************************************)

(* here, you could keep going and get a suspended one ... *)
let rec value_to_cyl_typ (cat : value) : (value * value cyl_typ , string) Result.t =
  match cat with
  | ArrV bc ->
    Ok (bc , Emp)
  | HomV (cat',s,t) ->
    let* (bc,ct) = value_to_cyl_typ cat' in
    Ok (bc, ct |> ((baseV s, lidV s, coreV s),
                   (baseV t, lidV t, coreV t)))
  | _ -> Error "Not a cylinder type"

let rec value_unhom (cat : value) : (value * value sph) =
  match cat with
  | HomV (cat',src,tgt) ->
    let (bc,sph) = value_unhom cat' in
    (bc, sph |> (src,tgt))
  | ObjV bc -> (bc,Emp)
  | _ -> (cat,Emp)

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


              



