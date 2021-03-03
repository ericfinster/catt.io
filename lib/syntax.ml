(*****************************************************************************)
(*                                                                           *)
(*                                   Syntax                                  *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
    
open Base
open Suite

(* Monadic bind for errors in scope *)
let (let*) m f = Base.Result.bind m ~f 

(*****************************************************************************)
(*                                 Raw Syntax                                *)
(*****************************************************************************)

type icit =
  | Impl
  | Expl

type name = string

type 'a tele = (name * icit * 'a) suite
    
type expr =
  | VarE of name
  | LamE of name * icit * expr
  | AppE of expr * expr * icit
  | PiE of name * icit * expr * expr
  | ObjE of expr
  | HomE of expr * expr * expr
  | CohE of expr tele * expr
  | CylE of expr * expr * expr
  | BaseE of expr
  | LidE of expr
  | CoreE of expr 
  | ArrE of expr
  | CatE
  | TypE
  | HoleE

type defn =
  | TermDef of name * expr tele * expr * expr
  | CohDef of name * expr tele * expr

(*****************************************************************************)
(*                         Pretty Printing Raw Syntax                        *)
(*****************************************************************************)
           
let is_app e =
  match e with
  | AppE (_, _, _) -> true
  | _ -> false

let is_pi e =
  match e with
  | PiE (_,_,_,_) -> true
  | _ -> false

let pp_tele pp_el ppf tl =
  let pp_trpl ppf (nm,ict,t) =
    match ict with
    | Expl -> pf ppf "(%s : %a)" nm pp_el t
    | Impl -> pf ppf "{%s : %a}" nm pp_el t
  in pp_suite pp_trpl ppf tl 

let rec pp_expr_gen show_imp ppf expr =
  let ppe = pp_expr_gen show_imp in 
  match expr with
  | VarE nm -> string ppf nm
  | LamE (nm,Impl,bdy) -> pf ppf "\\{%s}. %a" nm ppe bdy
  | LamE (nm,Expl,bdy) -> pf ppf "\\%s. %a" nm ppe bdy
  | AppE (u, v, Impl) ->
    if show_imp then 
      pf ppf "%a {%a}" ppe u ppe v
    else
      pf ppf "%a" ppe u 
  | AppE (u, v, Expl) ->
    let pp_v = if (is_app v) then
        parens ppe
      else ppe in 
    pf ppf "%a %a" ppe u pp_v v
  | PiE (nm,Impl,dom,cod) ->
    pf ppf "{%s : %a} -> %a" nm
      ppe dom ppe cod
  | PiE (nm,Expl,a,b) when Poly.(=) nm "" ->
    let pp_a = if (is_pi a) then
        parens ppe
      else ppe in 
    pf ppf "%a -> %a" 
      pp_a a ppe b
  | PiE (nm,Expl,dom,cod) ->
    pf ppf "(%s : %a) -> %a" nm
      ppe dom ppe cod
  | ObjE e -> pf ppf "[%a]" ppe e
  | HomE (_,s,t) ->
    (* pf ppf "%a | %a => %a" ppe c ppe s ppe t *)
    pf ppf "%a => %a" ppe s ppe t
  | CohE (g,a) ->
    pf ppf "coh @[[ %a : %a ]@]" (pp_tele ppe) g ppe a
  | CylE (b,l,c) ->
    pf ppf "[| %a | %a | %a |]" ppe b ppe l ppe c 
  | BaseE c ->
    pf ppf "base %a" ppe c
  | LidE c ->
    pf ppf "lid %a" ppe c
  | CoreE c ->
    pf ppf "core %a" ppe c 
  | ArrE c ->
    pf ppf "Arr %a" ppe c
  | CatE -> string ppf "Cat"
  | TypE -> string ppf "U"
  | HoleE -> string ppf "_"

let pp_expr = pp_expr_gen false
let pp_expr_with_impl = pp_expr_gen true
    
(*****************************************************************************)
(*                              Internal Syntax                              *)
(*****************************************************************************)

type idx = int
type mvar = int

type term =
  | VarT of idx
  | TopT of name 
  | LamT of name * icit * term
  | AppT of term * term * icit
  | PiT of name * icit * term * term
  | ObjT of term
  | HomT of term * term * term
  | CohT of term tele * term
  | CylT of term * term * term
  | BaseT of term
  | LidT of term
  | CoreT of term 
  | ArrT of term
  | CatT
  | TypT
  | MetaT of mvar
  | InsMetaT of mvar 
    
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
  | ObjT c -> ObjE (tte nms c)
  | HomT (c,s,t) ->
    HomE (tte nms c, tte nms s, tte nms t)
  | CohT (g,a) ->

    let rec go g nms m =
      match g with
      | Emp -> m nms Emp
      | Ext (g',(nm,ict,ty)) ->
        go g' nms (fun nms' ge' ->
            let e = tte nms' ty in
            m (Ext (nms',nm))
              (Ext (ge',(nm,ict,e))))

    in go g nms (fun nms' ge' -> CohE (ge' , tte nms' a))

  | CylT (b,l,c) ->
    CylE (tte nms b, tte nms l, tte nms c)
  | BaseT c -> BaseE (tte nms c)
  | LidT c -> LidE (tte nms c)
  | CoreT c -> CoreE (tte nms c)
  | ArrT c -> ArrE (tte nms c)
  | CatT -> CatE 
  | TypT -> TypE
  | MetaT _ -> HoleE
  (* Somewhat dubious, since we lose the implicit application ... *)
  | InsMetaT _ -> HoleE

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
(*                      Pretty printing internal syntax                      *)
(*****************************************************************************)

let is_app_tm tm =
  match tm with
  | AppT (_,_,_) -> true
  | _ -> false

let is_pi_tm tm =
  match tm with
  | PiT (_,_,_,_) -> true
  | _ -> false
    
let rec pp_term ppf tm =
  match tm with
  | VarT i -> int ppf i
  | TopT nm -> string ppf nm 
  | LamT (nm,Impl,t) ->
    pf ppf "\\{%s}. %a" nm pp_term t
  | LamT (nm,Expl,t) ->
    pf ppf "\\%s. %a" nm pp_term t
  | AppT (u,v,Impl) ->
    pf ppf "%a {%a}" pp_term u pp_term v
  | AppT (u,v,Expl) ->
    let pp_v = if (is_app_tm v) then
        parens pp_term
      else pp_term in 
    pf ppf "%a %a" pp_term u pp_v v
  | PiT (nm,Impl,a,p) ->
    pf ppf "{%s : %a} -> %a" nm
      pp_term a pp_term p
  | PiT (nm,Expl,a,p) when Poly.(=) nm "" ->
    let pp_a = if (is_pi_tm a) then
        parens pp_term
      else pp_term in 
    pf ppf "%a -> %a" 
      pp_a a pp_term p
  | PiT (nm,Expl,a,p) ->
    pf ppf "(%s : %a) -> %a" nm
      pp_term a pp_term p
  | ObjT c ->
    pf ppf "[%a]" pp_term c
  | HomT (c,s,t) ->
    pf ppf "%a | %a => %a" pp_term c pp_term s pp_term t
  | CohT (g,a) ->
    pf ppf "coh @[[ %a : %a ]@]" (pp_tele pp_term) g pp_term a
  | CylT (b,l,c) ->
    pf ppf "[| %a | %a | %a |]" pp_term b pp_term l pp_term c
  | BaseT c -> pf ppf "base %a" pp_term c
  | LidT c -> pf ppf "lid %a" pp_term c
  | CoreT c -> pf ppf "core %a" pp_term c
  | ArrT c -> pf ppf "Arr %a" pp_term c
  | CatT -> pf ppf "Cat"
  | TypT -> pf ppf "U"
  | MetaT _ -> pf ppf "_"
  (* Again, misses some implicit information ... *)
  | InsMetaT _ -> pf ppf "*_*"

(*****************************************************************************)
(*                                   Values                                  *)
(*****************************************************************************)

type lvl = int

type value =
  | FlexV of mvar * spine
  | RigidV of lvl * spine
  | TopV of name * spine * value 
  | LamV of name * icit * closure
  | PiV of name * icit * value * closure 
  | ObjV of value
  | HomV of value * value * value
  | CohV of value * spine
  | CylV of value * value * value
  | ArrV of value
  | CatV
  | TypV 

and spine =
  | EmpSp
  | AppSp of spine * value * icit
  | BaseSp of spine
  | LidSp of spine
  | CoreSp of spine

and top_env = (name * value) suite
and loc_env = value suite
and closure =
  | Closure of top_env * loc_env * term

let varV k = RigidV (k,EmpSp)

let rec pp_value ppf v =
  match v with
  | FlexV (m,sp) ->
    pf ppf "?%d %a" m pp_spine sp
  | RigidV (i,EmpSp) -> pf ppf "%d" i 
  | RigidV (i,sp) -> pf ppf "%d %a" i pp_spine sp
  | TopV (nm,sp,_) ->
    pf ppf "%s %a" nm pp_spine sp
  | LamV (nm,Expl,Closure (_,_,bdy)) ->
    pf ppf "\\%s.<%a>" nm pp_term bdy
  | LamV (nm,Impl,Closure (_,_,bdy)) ->
    pf ppf "\\{%s}.<%a>" nm pp_term bdy
  | PiV (nm,Expl,a,Closure (_,_,bdy)) ->
    pf ppf "(%s : %a) -> <%a>" nm
      pp_value a pp_term bdy
  | PiV (nm,Impl,a,Closure (_,_,bdy)) -> 
    pf ppf "{%s : %a} -> <%a>" nm
      pp_value a pp_term bdy
  | ObjV c ->
    pf ppf "[%a]" pp_value c
  | HomV (_,s,t) ->
    pf ppf "%a => %a" pp_value s pp_value t
  | CohV (v,sp) -> 
    pf ppf "coh @[%a@] %a" 
      pp_value v pp_spine sp
  | CylV (b,l,c) ->
    pf ppf "[| %a | %a | %a |]"
      pp_value b pp_value l pp_value c
  | ArrV c ->
    pf ppf "Arr %a" pp_value c
  | CatV -> pf ppf "Cat"
  | TypV -> pf ppf "U"

and pp_spine ppf sp =
  match sp with
  | EmpSp -> ()
  | AppSp (sp',v,Expl) ->
    pf ppf "%a %a" pp_spine sp' pp_value v
  | AppSp (sp',v,Impl) ->
    pf ppf "%a {%a}" pp_spine sp' pp_value v
  | BaseSp sp' -> 
    pf ppf "base %a" pp_spine sp'
  | LidSp sp' ->
    pf ppf "lid %a" pp_spine sp'
  | CoreSp sp' ->
    pf ppf "core %a" pp_spine sp'

let pp_top_env = hovbox (pp_suite (parens (pair ~sep:(any " : ") string pp_value)))
let pp_loc_env = hovbox (pp_suite ~sep:comma pp_value)

(*****************************************************************************)
(*                           Metavariable Context                            *)
(*****************************************************************************)

type meta_entry =
  | Solved of value
  | Unsolved

type metamap = (mvar,meta_entry,Int.comparator_witness) Map.t

let next_meta : int ref = ref 0
    
let metacontext : metamap ref =
  ref (Map.empty (module Int))

exception Meta_error of string
    
let lookup_meta m =
  let mctx = ! metacontext in
  match Map.find mctx m with
  | Some mentry -> mentry
  | None -> raise (Meta_error "unrecognized metavariable")

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

exception Eval_error of string

let rec eval top loc tm =
  (* pr "Evaluating: %a@," pp_term tm; *)
  match tm with
  | VarT i ->
    (try db_get i loc
     with Lookup_error ->
       raise (Eval_error (str "Index out of range: %d" i)))
  | TopT nm -> TopV (nm,EmpSp,(
      try assoc nm top
      with Lookup_error ->
        raise (Eval_error (str "Unknown id during eval: %s" nm))        
    ))
  | LamT (nm,ict,u) -> LamV (nm, ict, Closure (top,loc,u))
  | AppT (u,v,ict) -> appV (eval top loc u) (eval top loc v) ict
  | PiT (nm,ict,u,v) -> PiV (nm, ict, eval top loc u, Closure (top,loc,v))
  | ObjT c -> ObjV (eval top loc c)
  | HomT (c,s,t) ->
    HomV (eval top loc c, eval top loc s, eval top loc t)
  | CohT (g,a) -> CohV (eval top loc (tele_to_pi g a),EmpSp)
  | CylT (b,l,c) -> CylV (eval top loc b, eval top loc l, eval top loc c)
  | BaseT c -> baseV (eval top loc c)
  | LidT c -> lidV (eval top loc c)
  | CoreT c -> coreV (eval top loc c)
  | ArrT c -> ArrV (eval top loc c)
  | CatT -> CatV
  | TypT -> TypV
  | MetaT m -> metaV m
  | InsMetaT m -> appLocV loc (metaV m)

and metaV m =
  match lookup_meta m with
  | Unsolved -> FlexV (m, EmpSp)
  | Solved v -> v 

and ($$) c v =
  match c with
  | Closure (top,loc,tm) -> eval top (Ext (loc,v)) tm 

and appV t u ict =
  match t with
  | FlexV (m,sp) -> FlexV (m,AppSp(sp,u,ict))
  | RigidV (i,sp) -> RigidV (i,AppSp(sp,u,ict))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u,ict),appV tv u ict)
  | CohV (v,sp) -> CohV (v,AppSp(sp,u,ict))
  | LamV (_,_,cl) -> cl $$ u
  | _ -> raise (Eval_error "malformed application")

and baseV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,BaseSp sp)
  | RigidV (i,sp) -> RigidV (i,BaseSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,BaseSp sp, baseV tv)
  | CohV (ga,sp) -> CohV (ga,BaseSp sp)
  | CylV (b,_,_) -> b 
  | _ -> raise (Eval_error "malformed base projection")

and lidV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,LidSp sp)
  | RigidV (i,sp) -> RigidV (i,LidSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,LidSp sp, lidV tv)
  | CohV (ga,sp) -> CohV (ga,LidSp sp)
  | CylV (_,l,_) -> l
  | _ -> raise (Eval_error "malformed lid projection")

and coreV v =
  match v with
  | FlexV (m,sp) -> FlexV (m,CoreSp sp)
  | RigidV (i,sp) -> RigidV (i,CoreSp sp)
  | TopV (nm,sp,tv) -> TopV (nm,CoreSp sp, coreV tv)
  | CohV (ga,sp) -> CohV (ga,CoreSp sp)
  | CylV (_,_,c) -> c
  | _ -> raise (Eval_error "malformed core projection")

and appLocV loc v =
  match loc with
  | Emp -> v
  | Ext (loc',u) -> appV (appLocV loc' v) u Expl

let rec runSpV v sp =
  match sp with
  | EmpSp -> v
  | AppSp (sp',u,ict) -> appV (runSpV v sp') u ict
  | BaseSp sp' -> baseV (runSpV v sp')
  | LidSp sp' -> lidV (runSpV v sp')
  | CoreSp sp' -> coreV (runSpV v sp')

let rec force_meta v =
  match v with
  | FlexV (m,sp) ->
    (match lookup_meta m with
     | Unsolved -> FlexV (m,sp)
     | Solved v -> force_meta (runSpV v sp))
  | _ -> v

(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

let lvl_to_idx k l = k - l - 1

let rec quote k v ufld =
  let qc x = quote k x ufld in
  let qcs x s = quote_sp k x s ufld in 
  match force_meta v with
  | FlexV (m,sp) -> qcs (MetaT m) sp 
  | RigidV (l,sp) -> qcs (VarT (lvl_to_idx k l)) sp 
  | TopV (_,_,tv) when ufld -> qc tv 
  | TopV (nm,sp,_) -> qcs (TopT nm) sp 
  | LamV (nm,ict,cl) -> LamT (nm, ict, quote (k+1) (cl $$ varV k) ufld)
  | PiV (nm,ict,u,cl) -> PiT (nm, ict, qc u, quote (k+1) (cl $$ varV k) ufld)
  | ObjV c -> ObjT (qc c)
  | HomV (c,s,t) -> HomT (qc c, qc s, qc t)
  | CohV (v,sp) ->

    let pi_tm = quote k v ufld in
    let (g,a) = pi_to_tele pi_tm in
    qcs (CohT (g,a)) sp 

  | CylV (b,l,c) -> CylT (qc b, qc l, qc c)
  | ArrV c -> ArrT (qc c)
  | CatV -> CatT
  | TypV -> TypT

and quote_sp k t sp ufld =
  let qc x = quote k x ufld in
  let qcs x s = quote_sp k x s ufld in 
  match sp with
  | EmpSp -> t
  | AppSp (sp',u,ict) ->
    AppT (qcs t sp',qc u,ict)
  | BaseSp sp' -> BaseT (qcs t sp')
  | LidSp sp' -> LidT (qcs t sp')
  | CoreSp sp' -> CoreT (qcs t sp')

let nf top loc tm =
  quote (length loc) (eval top loc tm) true

(*****************************************************************************)
(*                                Unification                                *)
(*****************************************************************************)

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
    | CohV (v,sp) ->

      let pi_tm = go pr v in
      let (g,a) = pi_to_tele pi_tm in
      goSp pr (CohT (g,a)) sp
        
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
  (* pr "Meta solution : ?%d = %a@," m pp_value sol; *)
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
  | (TopV (_,sp,_) , TopV (_,sp',_)) when Poly.(=) stgy UnfoldNone ->
    unifySp UnfoldNone top l sp sp'
  | (TopV (_,sp,tv) , TopV (_,sp',tv')) when Poly.(=) stgy OneShot ->
    (try unifySp UnfoldNone top l sp sp'
     with Unify_error _ -> unify UnfoldAll top l tv tv')
      
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

  | (CohV (ga,sp), CohV (ga',sp')) ->
    unify stgy top l ga ga';
    unifySp stgy top l sp sp'

  | _ -> raise (Unify_error "could not unify")

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

(*****************************************************************************)
(*                                  Contexts                                 *)
(*****************************************************************************)

type bd =
  | Bound
  | Defined
    
type ctx = {
  top : top_env;
  loc : loc_env;
  lvl : lvl;
  types : (name * (bd * value)) suite;
}

let empty_ctx = {
  top = Emp;
  loc = Emp;
  lvl = 0;
  types = Emp;
}
 
let bind gma nm ty =
  let l = gma.lvl in {
    loc = Ext (gma.loc, varV l);
    top = gma.top;
    lvl = l+1;
    types = Ext (gma.types,(nm,(Bound,ty)));
  }

let define gma nm tm ty = {
  loc = gma.loc;
  top = Ext (gma.top,(nm,tm));
  lvl = gma.lvl;
  types = Ext (gma.types,(nm,(Defined,ty)));
}

let names gma =
  map_suite gma.types ~f:fst
    
(*****************************************************************************)
(*                           Context/Pd Conversion                           *)
(*****************************************************************************)

let rec underlying_cat v =
  match v with
  | HomV (c,_,_) ->
    let (cat,dim) = underlying_cat c in
    (cat,dim+1)
  | _ -> (v,0)

let rec nth_tgt i ty tm =
  if (i = 0) then Ok (ty, tm) else
    match ty with
    | HomV (c,_,t) ->
      nth_tgt (i-1) c t
    | _ -> Error "No target"

let unobj v =
  match v with
  | ObjV v' -> Ok v'
  | _ -> Error (str "Not a type of objects: %a" pp_value v)

let ctx_to_pd loc = 
  let rec go l loc =
    (* pr "Trying pasting context: @[<hov>%a@]@," (pp_suite pp_value) loc; *)
    match loc with
    | Emp -> Error "Empty context is not a pasting diagram"
    | Ext(Emp,_) -> Error "Singleton context is not a pasting diagram"
    | Ext(Ext(Emp,CatV),ObjV (RigidV (0,EmpSp))) ->
      Ok (Pd.Br (l,Emp),varV 0,varV 1,2,0)
    | Ext(Ext(loc',tobj),fobj) ->

      let* tty = unobj tobj in
      let* fty = unobj fobj in

      let* (pd,sty,stm,k,dim) = go (l+2) loc' in
      let (_,tdim) = underlying_cat tty in
      let codim = dim - tdim in
      let* (sty',stm') = nth_tgt codim sty stm in

      if (Poly.(<>) sty' tty) then

        let msg = str 
            "@[<v>Source and target types incompatible.
                  @,Source: %a
                  @,Target: %a@]"
            pp_value sty' pp_value tty
        in Error msg

      else let ety = HomV (sty',stm',varV k) in
        if (Poly.(<>) ety fty) then 

          let msg = str
              "@[<v>Incorrect filling type.
                    @,Expected: %a
                    @,Provided: %a@]"
              pp_value ety
              pp_value fty
          in Error msg

        else let* pd' = Pd.insert pd tdim (l+1)
                 (Pd.Br (l, Emp)) in
          Ok (pd', fty, varV (k+1), k+2, tdim+1)
  in go 0 loc

(*****************************************************************************)
(*                                   Debug                                   *)
(*****************************************************************************)

let rec quote_tele ufld typs =
  match typs with
  | Emp -> (Emp,0)
  | Ext (typs', (nm, (Defined,typ))) ->
    let (res_typs, l) = quote_tele ufld typs' in
    let typ_tm = quote l typ ufld in
    (Ext (res_typs,(nm,typ_tm)),l)
  | Ext (typs', (nm, (_,typ))) ->
    let (res_typs, l) = quote_tele ufld typs' in
    let typ_tm = quote l typ ufld in
    (Ext (res_typs,(nm, typ_tm)),l+1)
    
let dump_ctx ufld gma =
  let (tl,_) = quote_tele ufld gma.types in 
  pr "Context: @[<hov>%a@]@,"
    (pp_suite (parens (pair ~sep:(any " : ") string pp_term))) tl

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
  | CohT (g,a) ->
    let rec go k g =
      match g with
      | Emp -> free_vars k a
      | Ext (g',_) -> go (k+1) g'
    in go k g
  | CylT (b,l,c) ->
    Set.union (free_vars k b) (Set.union (free_vars k l) (free_vars k c))
  | BaseT c -> free_vars k c
  | LidT c -> free_vars k c
  | CoreT c -> free_vars k c
  | ArrT c -> free_vars k c
  | CatT -> fvs_empty
  | TypT -> fvs_empty
  | MetaT _ -> fvs_empty
  | InsMetaT _ -> fvs_empty

let rec free_vars_val k v =
  let fvc x = free_vars_val k x in 
  let sp_vars sp = free_vars_sp k sp in 
  match force_meta v with
  | FlexV (_,sp) -> sp_vars sp
  | RigidV (l,sp) -> Set.add (sp_vars sp) (lvl_to_idx k l) 
  | TopV (_,sp,_) -> sp_vars sp
  | LamV (_,_,Closure (_,loc,tm)) -> free_vars (length loc) tm
  | PiV (_,_,a,Closure (_,loc,b)) ->
    Set.union (free_vars_val k a) (free_vars (length loc) b)
  | ObjV c -> free_vars_val k c
  | HomV (c,s,t) ->
    Set.union_list (module Int) [fvc c; fvc s; fvc t]
  | CohV (v,sp) ->
    Set.union (free_vars_val k v) (sp_vars sp)
  | CylV (b,l,c) ->
    Set.union_list (module Int) [fvc b; fvc l; fvc c]
  | ArrV c -> fvc c
  | CatV -> fvs_empty
  | TypV -> fvs_empty 

and free_vars_sp k sp =
  let fvc x = free_vars_val k x in 
  let fvcs x = free_vars_sp k x in 
  match sp with
  | EmpSp -> fvs_empty
  | AppSp (sp',u,_) ->
    Set.union (fvcs sp') (fvc u)
  | BaseSp sp' -> fvcs sp'
  | LidSp sp' -> fvcs sp'
  | CoreSp sp' -> fvcs sp'

(*****************************************************************************)
(*                                 Cylinders                                 *)
(*****************************************************************************)

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

(*****************************************************************************)
(*                                Typechecking                               *)
(*****************************************************************************)

let fresh_meta _ =
  let mctx = ! metacontext in
  let m = ! next_meta in
  next_meta := m + 1;
  (* pr "next meta set to: %d@," (! next_meta); *)
  metacontext := Map.set mctx ~key:m ~data:Unsolved;
  InsMetaT m

let rec insert' gma m =
  let* (tm, ty) = m in 
  match force_meta ty with
  | PiV (_,Impl,_,b) ->
    let m = fresh_meta () in
    let mv = eval gma.top gma.loc m in
    insert' gma (Ok (AppT (tm,m,Impl) , b $$ mv))
  | _ -> Ok (tm, ty)

let insert gma m =
  let* (tm, ty) = m in 
  match tm with
  | LamT (_,Impl,_) -> Ok (tm, ty)
  | _ -> insert' gma (Ok (tm, ty))

type typing_error = [
  | `NameNotInScope of name
  | `IcityMismatch of icit * icit
  | `TypeMismatch of string
  | `PastingError of string
  | `FullnessError of string 
  | `InternalError
]

let rec check gma expr typ = 
  (* let typ_tm = quote gma.lvl typ false in
   * pr "Checking %a has type %a@," pp_expr expr pp_term typ_tm ;
   * dump_ctx true gma; *)
  match (expr, force_meta typ) with
  
  | (e , TopV (_,_,tv)) ->
    check gma e tv
  
  | (LamE (nm,i,e) , PiV (_,i',a,b)) when Poly.(=) i i' ->
    (* pr "canonical lambda@,"; *)
    let* bdy = check (bind gma nm a) e (b $$ varV gma.lvl) in
    Ok (LamT (nm,i,bdy))
  
  | (t , PiV (nm,Impl,a,b)) ->
    (* pr "non-canonical lambda@,"; *)
    let* bdy = check (bind gma nm a) t (b $$ varV gma.lvl) in
    Ok (LamT (nm,Impl,bdy))

  | (CylE (b,l,c) , ObjV cat) ->

    let* b_typ = base_type cat in 
    let* b' = check gma b b_typ in
    let bv = eval gma.top gma.loc b' in
    let* l_typ = lid_type cat in 
    let* l' = check gma l l_typ in
    let lv = eval gma.top gma.loc l' in
    (* And now, the harder one .... *)
    let* c' = check gma c (ObjV (HomV (cat,bv,lv))) in
    Ok (CylT (b',l',c'))

  | (HoleE , _) -> (* pr "fresh meta@,"; *)
    let mv = fresh_meta () in Ok mv
  
  | (e, expected) -> 
    (* pr "switching mode@,";
     * pr "e: %a@," pp_expr e;
     * pr "exp: %a@," pp_term (quote gma.lvl expected false); *)
    let* (e',inferred) = insert gma (infer gma e) in
    try unify OneShot gma.top gma.lvl expected inferred ; Ok e'
    with Unify_error _ ->
      let nms = names gma in 
      let inferred_nf = term_to_expr nms (quote gma.lvl inferred false) in
      let expected_nf = term_to_expr nms (quote gma.lvl expected false) in 
      let msg = str "@[<v>Type mismatch:@,Expression: %a@,Expected: %a@,Inferred: %a@,@]"
          pp_expr e pp_expr expected_nf pp_expr inferred_nf
      in Error (`TypeMismatch msg) 

and infer gma expr = 
  (* pr "Inferring type of %a@," pp_expr expr ;
   * dump_ctx true gma; *)
  match expr with
  
  | VarE nm -> (
      try
        let (idx,(b,typ)) = assoc_with_idx nm gma.types in
        match b with
        | Bound ->
          (* pr "Inferred variable of index %d to have type: %a@," idx pp_term (quote gma.lvl typ true) ; *)
          Ok (VarT idx, typ)
        | Defined ->
          (* pr "Inferred definition %s to have type: %a@," nm pp_term (quote gma.lvl typ true) ; *)
          Ok (TopT nm, typ)
      with Lookup_error -> Error (`NameNotInScope nm)
    )
  
  | LamE (nm,ict,e) ->
    let a = eval gma.top gma.loc (fresh_meta ()) in
    let* (e', t) = insert gma (infer (bind gma nm a) e) in
    Ok (LamT (nm,ict,e') , PiV (nm,ict,a,Closure (gma.top,gma.loc,quote (gma.lvl + 1) t false)))
  
  | AppE (u,v,ict) ->
    let* (u',ut) = match ict with
      | Impl -> infer gma u
      | Expl -> insert' gma (infer gma u)
    in
  
    let* (a,b) = match force_meta ut with
      | PiV (_,ict',a,b) ->
        if (Poly.(<>) ict ict') then
          Error (`IcityMismatch (ict,ict'))
        else Ok (a,b)
      | _ ->
        let a = eval gma.top gma.loc (fresh_meta ()) in
        let b = Closure (gma.top,gma.loc,fresh_meta ()) in
        unify OneShot gma.top gma.lvl ut (PiV ("x",ict,a,b)); 
        Ok (a,b)
    in let* v' = check gma v a in 
    Ok (AppT (u', v', ict) , b $$ eval gma.top gma.loc v')
  
  | PiE (nm,ict,a,b) ->
    let* a' = check gma a TypV in
    let* b' = check (bind gma nm (eval gma.top gma.loc a')) b TypV in
    Ok (PiT (nm,ict,a',b') , TypV)
  
  | ObjE c ->
    let* c' = check gma c CatV in
    Ok (ObjT c', TypV)
    
  | HomE (c,s,t) ->
    let* c' = check gma c CatV in
    let cv = eval gma.top gma.loc c' in
    let* s' = check gma s (ObjV cv) in
    let* t' = check gma t (ObjV cv) in
    Ok (HomT (c',s',t'), CatV)

  | CohE (g,a) ->
    let* (gt,at) = check_coh gma g a in
    let coh_ty = eval gma.top gma.loc (tele_to_pi gt (ObjT at)) in
    Ok (CohT (gt,at) , coh_ty)

  | CylE (_,_,_) -> Error `InternalError
  | BaseE _ -> Error `InternalError
  | LidE _ -> Error `InternalError
  | CoreE _ -> Error `InternalError

  | ArrE c -> 
    let* c' = check gma c CatV in
    Ok (ArrT c' , CatV)
      
  | CatE -> Ok (CatT , TypV)
  | TypE -> Ok (TypT , TypV)
  
  | HoleE ->
    let a = eval gma.top gma.loc (fresh_meta ()) in
    let t = fresh_meta () in
    Ok (t , a)

and with_tele gma tl m =
  match tl with
  | Emp -> m gma Emp Emp
  | Ext (tl',(id,ict,ty)) ->
    with_tele gma tl' (fun g tv tt ->
        let* ty_tm = check g ty TypV in
        let ty_val = eval g.top g.loc ty_tm in 
        m (bind g id ty_val)
          (Ext (tv,ty_val))
          (Ext (tt,(id,ict,ty_tm))))

and check_coh gma g a =
  with_tele gma g (fun gma' gv gt ->
      match ctx_to_pd gv with
      | Ok (pd,_,_,_,_) ->

        pr "Valid pasting context!@,";
        let* a' = check gma' a CatV in
        (* pr "return type: %a@," pp_term a'; *)
        let av = eval gma'.top gma'.loc a' in 
        let (ucat,bdim) = underlying_cat av in
        let cat_lvl = (length gma'.loc) - (length gv) in
        let cat_idx = length gv - 1 in 
        (* pr "cat_lvl: %d@," cat_lvl; *)
        (try unify OneShot gma'.top gma'.lvl (varV cat_lvl) ucat;
           
           (match av with
            | HomV (c,s,t) ->

              let k = length gma'.loc in 
              let cat_vars = free_vars_val k c in
              let src_vars = free_vars_val k s in
              let tgt_vars = free_vars_val k t in
              let pd_dim = Pd.dim_pd pd in 

              (* pr "bdim: %d@," bdim;
               * pr "pd_dim: %d@," pd_dim;
               * pr "cat_vars: @[%a@]@," (list ~sep:(any ", ") int) (Set.to_list cat_vars);
               * pr "src_vars: @[%a@]@," (list ~sep:(any ", ") int) (Set.to_list src_vars);
               * pr "tgt_vars: @[%a@]@," (list ~sep:(any ", ") int) (Set.to_list tgt_vars); *)

              if (bdim > pd_dim) then

                let pd_vars = Set.of_list (module Int) (cat_idx::to_list (Pd.labels pd)) in
                let tot_vars = Set.union cat_vars (Set.union src_vars tgt_vars) in

                (* pr "cat_idx: %d@," cat_idx;
                 * pr "pd_vars: @[<hov>%a@]@," (list ~sep:(any ", ") int) (Set.to_list pd_vars);
                 * pr "tot_vars: @[<hov>%a@]@," (list ~sep:(any ", ") int) (Set.to_list tot_vars); *)
                
                if (not (Set.is_subset pd_vars ~of_:tot_vars)) then
                  Error (`FullnessError "coherence case is not full")                 
                else Ok (gt,a')

              else

                let pd_src = Pd.truncate true (pd_dim - 1) pd in
                let pd_tgt = Pd.truncate false (pd_dim - 1) pd in

                let pd_src_vars = Set.of_list (module Int) (cat_idx::to_list (Pd.labels pd_src)) in
                let pd_tgt_vars = Set.of_list (module Int) (cat_idx::to_list (Pd.labels pd_tgt)) in

                let tot_src_vars = Set.union cat_vars src_vars in
                let tot_tgt_vars = Set.union cat_vars tgt_vars in

                if (not (Set.is_subset pd_src_vars ~of_:tot_src_vars)) then
                  Error (`FullnessError "non-full source")
                else if (not (Set.is_subset pd_tgt_vars ~of_:tot_tgt_vars)) then
                  Error (`FullnessError "non-full target")
                else Ok (gt,a')

            | _ -> Error (`FullnessError "invalid coherence return type"))


         with Unify_error _ -> Error (`FullnessError "invalid base category"))

      | Error msg -> Error (`PastingError msg))


let rec abstract_tele_with_tm tl ty tm =
  match tl with
  | Emp -> (ty,tm)
  | Ext (tl',(nm,ict,expr)) ->
    abstract_tele_with_tm tl'
      (PiE (nm,ict,expr,ty)) (LamE (nm,ict,tm))
              
let rec check_defs gma defs =
  match defs with
  | [] -> Ok gma
  | (TermDef (id,tl,ty,tm))::ds ->
    pr "----------------@,";
    pr "Checking definition: %s@," id;
    let (abs_ty,abs_tm) = abstract_tele_with_tm tl ty tm in
    let* ty_tm = check gma abs_ty TypV in
    let ty_val = eval gma.top gma.loc ty_tm in
    let* tm_tm = check gma abs_tm ty_val in
    let tm_val = eval gma.top gma.loc tm_tm in 
    pr "Checking complete for %s@," id;
    let tm_nf = term_to_expr Emp (quote (gma.lvl) tm_val false) in
    let ty_nf = term_to_expr Emp (quote (gma.lvl) ty_val false) in
    pr "Type: %a@," pp_expr ty_nf;
    pr "Term: %a@," pp_expr tm_nf;
    check_defs (define gma id tm_val ty_val) ds
  | (CohDef (id,g,a))::ds ->
    pr "----------------@,";
    pr "Checking coherence: %s@," id;
    let* (gt,at) = check_coh gma g a in
    let coh_ty = eval gma.top gma.loc (tele_to_pi gt (ObjT at)) in
    let coh_tm = eval gma.top gma.loc (CohT (gt , at)) in
    let coh_ty_nf = term_to_expr Emp (quote gma.lvl coh_ty false) in
    let coh_tm_nf = term_to_expr Emp (quote gma.lvl coh_tm false) in
    pr "Coh type: %a@," pp_expr coh_ty_nf;
    (* pr "Coh term raw: %a@," pp_term (CohT (gt,at));
     * pr "Coh term val: %a@," pp_value coh_tm;
     * pr "Coh term nf: %a@," pp_term (quote gma.lvl coh_tm false); *)
    pr "Coh expr: %a@," pp_expr coh_tm_nf;
    check_defs (define gma id coh_tm coh_ty) ds


