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

let rec pp_expr ppf expr =
  match expr with
  | VarE nm -> string ppf nm
  | LamE (nm,Impl,bdy) -> pf ppf "\\{%s}. %a" nm pp_expr bdy
  | LamE (nm,Expl,bdy) -> pf ppf "\\%s. %a" nm pp_expr bdy
  | AppE (u, v, Impl) ->
    pf ppf "%a {%a}" pp_expr u pp_expr v
  | AppE (u, v, Expl) ->
    let pp_v = if (is_app v) then
        parens pp_expr
      else pp_expr in 
    pf ppf "%a %a" pp_expr u pp_v v
  | PiE (nm,Impl,dom,cod) ->
    pf ppf "{%s : %a} -> %a" nm
      pp_expr dom pp_expr cod
  | PiE (nm,Expl,a,b) when Poly.(=) nm "" ->
    let pp_a = if (is_pi a) then
        parens pp_expr
      else pp_expr in 
    pf ppf "%a -> %a" 
      pp_a a pp_expr b
  | PiE (nm,Expl,dom,cod) ->
    pf ppf "(%s : %a) -> %a" nm
      pp_expr dom pp_expr cod
  | ObjE e -> pf ppf "[%a]" pp_expr e
  | HomE (c,s,t) ->
    pf ppf "%a | %a => %a" pp_expr c pp_expr s pp_expr t
  | CohE (g,a) ->
    pf ppf "coh [ %a : %a ]" (pp_tele pp_expr) g pp_expr a
  | CatE -> string ppf "Cat"
  | TypE -> string ppf "U"
  | HoleE -> string ppf "_"
  
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
  | CatT
  | TypT
  | MetaT of mvar
  | InsMetaT of mvar 
    
let rec term_to_expr nms tm = 
  match tm with
  | VarT i ->
    let nm = db_get i nms in VarE nm
  | TopT nm -> VarE nm
  | LamT (nm,ict,bdy) ->
    LamE (nm, ict, term_to_expr (Ext (nms,nm)) bdy)
  | AppT (u,v,ict) ->
    AppE (term_to_expr nms u, term_to_expr nms v, ict)
  | PiT (nm,ict,a,b) ->
    PiE (nm, ict, term_to_expr nms a, term_to_expr (Ext (nms,nm)) b)
  | ObjT c -> ObjE (term_to_expr nms c)
  | HomT (c,s,t) ->
    HomE (term_to_expr nms c, term_to_expr nms s, term_to_expr nms t)
  | CohT (g,a) ->
    
    let rec go g nms a =
      match g with
      | Emp -> (Emp, term_to_expr nms a)
      | Ext (g',(nm,icit,ty)) ->
        let (rg,e) = go g' (Ext (nms,nm)) a in
        (Ext (rg,(nm,icit,term_to_expr nms ty)), e)
    in let r = go g nms a in CohE (fst r , snd r)

  | CatT -> CatE 
  | TypT -> TypE
  | MetaT _ -> HoleE
  (* Somewhat dubious, since we lose the implicit application ... *)
  | InsMetaT _ -> HoleE

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
  | HomT (_,s,t) ->
    pf ppf "%a => %a" pp_term s pp_term t
  | CohT (g,a) ->
    pf ppf "coh [ %a : %a ]" (pp_tele pp_term) g pp_term a
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
  | CohV of value tele * value * spine
  | CatV
  | TypV 

and top_env = (name * value) suite
and loc_env = value suite
and spine = (value * icit) suite

and closure =
  | Closure of top_env * loc_env * term

let varV k = RigidV (k,Emp)

let rec pp_value ppf v =
  match v with
  | FlexV (m,sp) ->
    pf ppf "?%d %a" m pp_spine sp
  | RigidV (i,Emp) -> pf ppf "%d" i 
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
  | CohV (g,a,sp) -> 
    pf ppf "coh [ %a : %a ] %a" (pp_tele pp_value) g
      pp_value a pp_spine sp
  | CatV -> pf ppf "Cat"
  | TypV -> pf ppf "U"

and pp_spine ppf sp =
  let pp_v ppf (v,ict) =
    match ict with
    | Expl -> pp_value ppf v
    | Impl -> pf ppf "{%a}" pp_value v
  in pp_suite pp_v ppf sp

let pp_top_env =
  hovbox (pp_suite (parens (pair ~sep:(any " : ") string pp_value)))

let pp_loc_env =
  hovbox (pp_suite ~sep:comma pp_value)


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
  | TopT nm -> TopV (nm,Emp,(
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
  | CohT (g,a) ->
    
    (* we trivially evaluate with variables *)
    let rec go g loc k a =
      match g with
      | Emp -> (Emp, eval top loc a)
      | Ext (g',(nm,icit,ty)) ->
        let (rg,v) = go g' (Ext (loc,varV k)) (k+1) a in
        (Ext (rg,(nm,icit,eval top loc ty)), v)
    in let r = go g loc (length loc) a in CohV (fst r , snd r, Emp)
    
  | CatT -> CatV
  | TypT -> TypV
  | MetaT m -> metaV m
  | InsMetaT m ->
    (* pr "Expanding meta %d with local context: %a@," m pp_loc_env loc;  *)
    appLocV loc (metaV m)

and metaV m =
  match lookup_meta m with
  | Unsolved -> FlexV (m, Emp)
  | Solved v -> v 

and ($$) c v =
  match c with
  | Closure (top,loc,tm) -> eval top (Ext (loc,v)) tm 

and appV t u ict =
  match t with
  | FlexV (m,sp) -> FlexV (m,Ext(sp,(u,ict)))
  | RigidV (i,sp) -> RigidV (i,Ext(sp,(u,ict)))
  | TopV (nm,sp,tv) -> TopV (nm,Ext(sp,(u,ict)),appV tv u ict)
  | CohV (g,a,sp) -> CohV (g,a,Ext(sp,(u,ict)))
  | LamV (_,_,cl) -> cl $$ u
  | PiV (_,_,_,_) -> raise (Eval_error "malformed app: pi")
  | ObjV _ -> raise (Eval_error "malformed app: obj")
  | HomV (_,_,_) -> raise (Eval_error "malformed app: hom")
  | CatV -> raise (Eval_error "malformed app: cat")
  | TypV -> raise (Eval_error "malformed app: typ")

and appLocV loc v =
  match loc with
  | Emp -> v
  | Ext (loc',u) -> appV (appLocV loc' v) u Expl

let rec appSpV v sp =
  match sp with
  | Emp -> v
  | Ext (sp',(u,ict)) -> appV (appSpV v sp') u ict

let rec force_meta v =
  match v with
  | FlexV (m,sp) ->
    (match lookup_meta m with
     | Unsolved -> FlexV (m,sp)
     | Solved v -> force_meta (appSpV v sp))
  | _ -> v

(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

let lvl_to_idx k l = k - l - 1

let rec quote k v ufld =
  match v with
  | FlexV (m,sp) -> quote_sp k (MetaT m) sp ufld
  | RigidV (l,sp) -> quote_sp k (VarT (lvl_to_idx k l)) sp ufld
  | TopV (_,_,tv) when ufld -> quote k tv ufld
  | TopV (nm,sp,_) -> quote_sp k (TopT nm) sp ufld
  | LamV (nm,ict,cl) -> LamT (nm, ict, quote (k+1) (cl $$ varV k) ufld)
  | PiV (nm,ict,u,cl) -> PiT (nm, ict, quote k u ufld, quote (k+1) (cl $$ varV k) ufld)
  | ObjV c -> ObjT (quote k c ufld)
  | HomV (c,s,t) -> HomT (quote k c ufld, quote k s ufld, quote k t ufld)
  | CohV (g,a,sp) ->

    let rec go g k a =
      match g with
      | Emp -> (Emp, quote k a ufld)
      | Ext (g',(nm,icit,ty)) ->
        let (rg,v) = go g' (k+1) a in
        (Ext (rg,(nm,icit,quote k ty ufld)), v)
    in let r = go g k a
    in quote_sp k (CohT (fst r , snd r)) sp ufld 
      
  | CatV -> CatT
  | TypV -> TypT

and quote_sp k t sp ufld =
  match sp with
  | Emp -> t
  | Ext (sp',(u,ict)) ->
    AppT (quote_sp k t sp' ufld, quote k u ufld, ict)

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
  let rec go = function
    | Emp -> (0, Map.empty (module Int))
    | Ext (sp',(u,_)) ->
      let (dom, ren) = go sp' in
      (match force_meta u with
       | RigidV (l,Emp) ->
         (match Map.add ren ~key:l ~data:dom  with
          | `Ok ren' -> (dom + 1,ren')
          | `Duplicate -> raise (Unify_error "non-linear pattern"))
       | _ -> raise (Unify_error "meta-var applied to non-bound-variable")) in 
  let (dom,ren) = go sp in
  { dom = dom ; cod = cod ; ren = ren }

let rename m pren v =

  let rec goSp pr v = function
    | Emp -> v
    | Ext (sp,(u,ict)) -> AppT (goSp pr v sp, go pr u, ict)

  and go pr v = match force_meta v with
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
    | CohV (g,a,sp) ->
      
      (* Are these all folds of a certain kind? *)
      let rec coh_go g a =
        match g with
        | Emp -> (Emp, go pr a)
        | Ext (g',(nm,icit,ty)) ->
          let (rg,v) = coh_go g' a in
          (Ext (rg,(nm,icit, go pr ty)), v)
      in let r = coh_go g a
      in goSp pr (CohT (fst r , snd r)) sp 
        
    | CatV -> CatT
    | TypV -> TypT

  in go pren v

let lams icts t =
  let rec go k icts t =
    match icts with
    | Emp -> t
    | Ext (is,i) -> 
      let nm = Printf.sprintf "x%d" (k+1) in
      LamT (nm, i, go (k+1) is t) 
  in go 0 icts t

let solve top k m sp v =
  let prn = invert k sp in
  let rhs = rename m prn v in
  let sol = eval top Emp (lams (rev (map_suite sp ~f:snd)) rhs) in
  let mctx = ! metacontext in
  pr "Meta solution : ?%d = %a@," m pp_value sol;
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

  | _ -> raise (Unify_error "could not unify")

and unifySp stgy top l sp sp' =
  match (sp,sp') with
  | (Emp,Emp) -> ()
  | (Ext (s,(u,_)),Ext(s',(u',_))) ->
    unifySp stgy top l s s';
    unify stgy top l u u'
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

(*****************************************************************************)
(*                           Context/Pd Conversion                           *)
(*****************************************************************************)

type pasting_error = [
  | `PastingError of string
]
    
let rec cat_dim v =
  match v with
  | RigidV(_,_) -> Ok 0
  | HomV (c,_,_) ->
    let* d = cat_dim c in 
    Ok (d + 1)
  | _ -> Error "Term has no valid dimension"

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

let rec ctx_to_pd loc =
  pr "Trying pasting context: @[<hov>%a@]@," (pp_suite pp_value) loc;
  match loc with
  | Emp -> Error "Empty context is not a pasting diagram"
  | Ext(Emp,_) -> Error "Singleton context is not a pasting diagram"
  | Ext(Ext(Emp,CatV),ObjV (RigidV (0,Emp))) ->
    Ok (Pd.Br (varV 1,Emp),varV 0,varV 1,2,0)
  | Ext(Ext(loc',tobj),fobj) ->

    let* tty = unobj tobj in
    let* fty = unobj fobj in

    let* (pd,sty,stm,k,dim) = ctx_to_pd loc' in
    let* tdim = cat_dim tty in
    let codim = dim - tdim in
    pr "codim: %d@," codim;
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

      else let* pd' = Pd.insert pd tdim (varV k)
               (Pd.Br (varV (k+1), Emp)) in
        Ok (pd', fty, varV (k+1), k+2, tdim+1)

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
  | `PastingError of string
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
  
  | (HoleE , _) -> (* pr "fresh meta@,"; *)
    let mv = fresh_meta () in Ok mv
  
  | (e, expected) ->
    (* pr "switching mode@,";
     * pr "e: %a@," pp_expr e;
     * pr "exp: %a@," pp_term (quote gma.lvl expected false); *)
    let* (e',inferred) = insert gma (infer gma e) in
    unify OneShot gma.top gma.lvl expected inferred ; Ok e'

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
  
  | CohE (_,_) -> Error `InternalError
    (* with_tele gma g (fun _ _ -> 
     *     raise (Typing_error "not done")
     *   ) *)
  
  | CatE -> Ok (CatT , TypV)
  | TypE -> Ok (TypT , TypV)
  
  | HoleE ->
    let a = eval gma.top gma.loc (fresh_meta ()) in
    let t = fresh_meta () in
    Ok (t , a)

and with_tele gma tl m =
  match tl with
  | Emp -> m gma Emp
  | Ext (tl',(id,_,ty)) ->
    with_tele gma tl' (fun g t ->
        let* ty' = check g ty TypV in
        let ty_v = eval g.top g.loc ty' in 
        m (bind g id ty_v)
          (Ext (t,ty_v)))

let rec abstract_tele tl ty tm =
  match tl with
  | Emp -> (ty,tm)
  | Ext (tl',(nm,ict,expr)) ->
    abstract_tele tl' (PiE (nm,ict,expr,ty)) (LamE (nm,ict,tm))
    
let rec check_defs gma defs =
  match defs with
  | [] -> Ok gma
  | (TermDef (id,tl,ty,tm))::ds ->
    pr "----------------@,";
    pr "Checking definition: %s@," id;
    let (abs_ty,abs_tm) = abstract_tele tl ty tm in
    let* ty_tm = check gma abs_ty TypV in
    let ty_val = eval gma.top gma.loc ty_tm in
    let* tm_tm = check gma abs_tm ty_val in
    let tm_val = eval gma.top gma.loc tm_tm in 
    pr "Checking complete for %s@," id;
    let tm_nf = term_to_expr Emp (quote (gma.lvl) tm_val true) in
    let ty_nf = term_to_expr Emp (quote (gma.lvl) ty_val false) in
    pr "Type: %a@," pp_expr ty_nf;
    pr "Term: %a@," pp_expr tm_nf;
    check_defs (define gma id tm_val ty_val) ds
  | (CohDef (nm,g,_))::ds ->
    pr "----------------@,";
    pr "Checking coherence: %s@," nm; 
    let* _ = with_tele gma g (fun _ gv ->
        match ctx_to_pd gv with
        | Ok (_,_,_,_,_) -> 
          pr "Valid pasting context!@,"; Ok ()
        | Error msg -> Error (`PastingError msg)
      ) in check_defs gma ds


