(*****************************************************************************)
(*                                                                           *)
(*                                Unification                                *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Syntax
open Value
open Term
open Eval
open Meta
    
type perm = (lvl,lvl,Int.comparator_witness) Map.t
                       
type partial_ren = {
  dom : lvl;
  cod : lvl;
  ren : perm;
}

let lift pren = {
  dom = pren.dom + 1;
  cod = pren.cod + 1;
  ren = Map.set pren.ren ~key:pren.cod ~data:pren.dom; 
}

exception Unify_error of string
    
let invert cod sp =

  let rec go sp =
    match sp with
    | EmpSp -> (0, Map.empty (module Int))
    | AppSp (sp',u,_) ->
      let (dom, ren) = go sp' in
      (match force_meta u with
       | RigidV (l,EmpSp) ->
         (match Map.add ren ~key:l ~data:dom  with
          | `Ok ren' -> (dom + 1,ren')
          | `Duplicate -> raise (Unify_error "non-linear pattern"))
       | _ -> raise (Unify_error "meta-var applied to non-bound-variable"))

    (* TODO: More sophisticated unification here? *)
    | BaseSp _ -> raise (Unify_error "base projected spine")
    | LidSp _ -> raise (Unify_error "lid projected spine")
    | CoreSp _ -> raise (Unify_error "core projected spine")

  in let (dom,ren) = go sp
  in { dom = dom ; cod = cod ; ren = ren }

let rename m pren v =

  let rec go pr v = match force_meta v with
    | FlexV (m',sp) ->
      if (m <> m') then
        goSp pr (MetaT m') sp
      else raise (Unify_error "failed occurs check")
    | RigidV (i,sp) ->
      (match Map.find pr.ren i with
       | Some l -> goSp pr (VarT (lvl_to_idx pr.dom l)) sp 
       | None -> raise (Unify_error "escaped variable"))
    (* We maximally unfold meta-solutions.  I think this is the only
       reasonable choice for top-level metas like we have here. *)
    | TopV (_,_,tv) -> go pr tv
    | LamV (nm,ict,a) -> LamT (nm, ict, go (lift pr) (a $$ varV pr.cod))
    | PiV (nm,ict,a,b) -> PiT (nm, ict, go pr a, go (lift pr) (b $$ varV pr.cod))
    | ObjV c -> ObjT (go pr c)
    | HomV (c,s,t) -> HomT (go pr c, go pr s, go pr t)

    | UCompV (uc,sp) ->
      goSp pr (term_ucomp_coh (ucmp_pd uc)) sp
    | CohV (v,sp) ->
      let pi_tm = go pr v in
      let (g,a) = pi_to_tele pi_tm in
      (match a with
       | HomT (c,s,t) -> goSp pr (CohT (g,c,s,t)) sp
       | _ -> raise (Failure "rename coh has invalid type"))
    | CylCohV _ -> raise (Failure "rename cylcoh")
      
    | CylV (b,l,c) -> CylT (go pr b, go pr l, go pr c)
    | ArrV c -> ArrT (go pr c)
    | CatV -> CatT
    | TypV -> TypT

  and goSp pr v sp =
    match sp with
    | EmpSp -> v
    | AppSp (sp',u,ict) -> AppT (goSp pr v sp', go pr u, ict)
    | BaseSp sp' -> BaseT (goSp pr v sp')
    | LidSp sp' -> LidT (goSp pr v sp')
    | CoreSp sp' -> CoreT (goSp pr v sp')

  in go pren v

let rec lams k sp t =
  match sp with
  | EmpSp -> t
  | AppSp (sp',_,ict) ->
    let nm = Printf.sprintf "x%d" k in
    lams (k+1) sp' (LamT (nm,ict,t))
  | BaseSp sp' -> lams k sp' t
  | LidSp sp' -> lams k sp' t
  | CoreSp sp' -> lams k sp' t

let solve top k m sp v =
  let prn = invert k sp in
  let rhs = rename m prn v in
  let sol = eval top Emp (lams 0 sp rhs) in
  let mctx = ! metacontext in
  (* pr "Meta solution : ?%d = @[%a@]@," m pp_value sol; *)
  metacontext := Map.update mctx m ~f:(fun _ -> Solved sol)

type strategy =
  | UnfoldAll
  | UnfoldNone
  | OneShot 

let rec unify stgy top l t u =
  match (force_meta t , force_meta u) with
  | (TypV , TypV) -> ()
  | (CatV , CatV) -> ()
                     
  | (LamV (_,_,a) , LamV (_,_,a')) -> unify stgy top (l+1) (a $$ varV l) (a' $$ varV l)
  | (t' , LamV(_,i,a')) -> unify stgy top (l+1) (appV t' (varV l) i) (a' $$ varV l)
  | (LamV (_,i,a) , t') -> unify stgy top (l+1) (a $$ varV l) (appV t' (varV l) i)
                     
  | (PiV (_,ict,a,b) , PiV (_,ict',a',b')) when Poly.(=) ict ict' ->
    unify stgy top l a a' ;
    unify stgy top (l+1) (b $$ varV l) (b' $$ varV l)
  | (PiV (_,_,_,_) , PiV (_,_,_,_)) ->
    raise (Unify_error "Icity mismatch")

  | (RigidV (i,sp) , RigidV (i',sp')) when i = i' -> unifySp stgy top l sp sp'
  | (RigidV (i,_) , RigidV (i',_)) ->
    raise (Unify_error (str "Rigid mismatch: %d =/= %d" (lvl_to_idx l i) (lvl_to_idx l i')))
      
  | (FlexV (m,sp) , FlexV (m',sp')) when m = m' -> unifySp stgy top l sp sp' 
  | (FlexV (m,_) , FlexV (m',_)) -> 
    raise (Unify_error (str "Flex mismatch: %d =/= %d" m m'))          
  | (t' , FlexV (m,sp)) when Poly.(<>) stgy UnfoldNone -> solve top l m sp t'
  | (_ , FlexV (_,_)) -> raise (Unify_error "refusing to solve meta")
  | (FlexV (m,sp) , t') when Poly.(<>) stgy UnfoldNone -> solve top l m sp t'
  | (FlexV (_,_) , _) -> raise (Unify_error "refusing to solve meta")

  | (TopV (_,_,tv) , TopV (_,_,tv')) when Poly.(=) stgy UnfoldAll ->
    unify UnfoldAll top l tv tv'
  | (TopV (nm,sp,_) , TopV (nm',sp',_)) when Poly.(=) stgy UnfoldNone ->
    if (Poly.(=) nm nm') then 
      unifySp UnfoldNone top l sp sp'
    else raise (Unify_error "top level name mismatch")
  | (TopV (nm,sp,tv) , TopV (nm',sp',tv')) when Poly.(=) stgy OneShot ->
    if (Poly.(=) nm nm') then 
      (try unifySp UnfoldNone top l sp sp'
       with Unify_error _ -> unify UnfoldAll top l tv tv')
    else unify UnfoldAll top l tv tv'
        
  | (TopV (_,_,_) , _) when Poly.(=) stgy UnfoldNone ->
    raise (Unify_error "refusing to unfold top level def")
  | (TopV (_,_,tv) , t') -> unify stgy top l tv t'

  | (_ , TopV (_,_,_)) when Poly.(=) stgy UnfoldNone ->
    raise (Unify_error "refusing to unfold top level def")
  | (t , TopV (_,_,tv')) -> unify stgy top l t tv'

  | (ObjV c, ObjV c') ->
    unify stgy top l c c'

  | (HomV (c,s,t), HomV (c',s',t')) ->
    unify stgy top l c c';
    unify stgy top l s s';
    unify stgy top l t t'

  | (ArrV c, ArrV c') ->
    unify stgy top l c c'

  | (CohV (ga,sp), CohV (ga',sp')) ->
    unify stgy top l ga ga';
    unifySp stgy top l sp sp'

  | (tm,um) ->
    let msg = str "Failed to unify: %a =/= %a"
        pp_value tm pp_value um in 
    raise (Unify_error msg)

and unifySp stgy top l sp sp' =
  match (sp,sp') with
  | (EmpSp, EmpSp) -> ()
  | (AppSp (s,u,_), AppSp (s',u',_)) ->
    unifySp stgy top l s s';
    unify stgy top l u u'
  | (BaseSp s , BaseSp s') ->
    unifySp stgy top l s s'
  | (LidSp s , LidSp s') ->
    unifySp stgy top l s s'
  | (CoreSp s , CoreSp s') ->
    unifySp stgy top l s s'
  | _ -> raise (Unify_error "spine mismatch")
