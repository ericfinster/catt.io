(*
 * typecheck.ml - catt typechecker
 *)

open Common
open Printf
open Term
open Pd   
   
type tc_def =
  | TCCellDef of cell_term
  | TCTermDef of ctx * ty_term * tm_term

type tc_env = {
    gma : (string * ty_term) list;
    rho : (string * tc_def) list;
  }

let empty_env = { gma = [] ; rho = [] }
              
(* The typechecking monad *)
type 'a tcm = tc_env -> 'a err

(* Bind for the typechecking monad *)
let ( >>= ) m f env =
  match m env with
  | Fail s -> Fail s
  | Succeed a -> f a env
               
let tc_ok a _ = Succeed a
let tc_fail msg _ = Fail msg
let tc_in_ctx g m env = m { env with gma = g }
let tc_ctx env = Succeed env.gma
let tc_with_cell id cell m env = m { env with rho = (id, TCCellDef cell) :: env.rho }
let tc_with_def id g ty tm m env = m { env with rho = (id, TCTermDef (g,ty,tm)) :: env.rho }
let tc_with_var id ty m env = m { env with gma = (id, ty) :: env.gma }
let tc_with_vars vars m env = m { env with gma = vars @ env.gma }
let tc_ctx_vars env = Succeed (List.map fst env.gma)
let tc_lift m_err _ = m_err
                    
let tc_try m f_ok f_fail env =
  match m with
  | Fail msg -> f_fail msg env
  | Succeed a -> f_ok a env
                    
let rec tc_traverse f = function
  | [] -> tc_ok []
  | (x::xs) -> tc_traverse f xs >>= fun rs ->
               f x >>= fun r ->
               tc_ok (r::rs)
                    
(* Lookup and identifier in the context *)
let tc_lookup_var ident env =
  try Succeed (List.assoc ident env.gma)
  with Not_found -> Fail (sprintf "Unknown identifier: %s" ident)

let tc_lookup_def ident env =
  try Succeed (List.assoc ident env.rho)
  with Not_found -> Fail (sprintf "Unknown cell identifier: %s" ident)

(* Find the k-th target of the given term an type *)
let rec tc_tgt_of a t k =
  if (k < 0) then
    tc_fail "Negative codimension"
  else if (k = 0) then
    tc_ok (a, t)
  else match t with
       | ObjT -> tc_fail "Object has no target"
       | ArrT (typ, _, tgt) -> tc_tgt_of tgt typ (k-1)

(* Source pasting diagram *)
let rec tc_pd_kth_src k pd =
  match pd with
  | [] -> tc_fail "Empty pasting diagram"
  | (id, ObjT) :: [] -> tc_ok ((id, ObjT) :: [])
  | (_, _) :: [] -> tc_fail "Malformed pasting diagram"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     if (dim_of tgt_typ >= k) then
       tc_pd_kth_src k pd'
     else
       tc_pd_kth_src k pd' >>= fun pd_src ->
       tc_ok ((fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd_src)

(* Target pasting diagram *)
let rec tc_pd_kth_tgt k pd =
  match pd with
  | [] -> tc_fail "Empty pasting diagram"
  | (id, ObjT) :: [] -> tc_ok ((id, ObjT) :: [])
  | (_, _) :: [] -> tc_fail "Malformed pasting diagram"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     let d = dim_of tgt_typ in
     if (d > k) then
       tc_pd_kth_tgt k pd'
     else tc_pd_kth_tgt k pd' >>= fun pd_tgt ->
          if (d = k) then
            match pd_tgt with
            | [] -> tc_fail "Empty pasting diagram target"
            | _ :: pd_tgt' -> tc_ok ((tgt_id, tgt_typ) :: pd_tgt')
          else tc_ok ((fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd_tgt)

let tc_pd_src pd = tc_pd_kth_src ((dim_of_pd pd) - 1) pd
let tc_pd_tgt pd = tc_pd_kth_tgt ((dim_of_pd pd) - 1) pd

(* Basic normalization (unfold definitions, uniquify pd's *)
let rec tc_simple_ty_nf ty =
  match ty with
  | ObjT -> tc_ok ObjT
  | ArrT (ty', src, tgt) ->
     tc_simple_ty_nf ty' >>= fun ty_nf ->
     tc_simple_tm_nf src >>= fun src_nf ->
     tc_simple_tm_nf tgt >>= fun tgt_nf ->
     tc_ok (ArrT (ty_nf, src_nf, tgt_nf))
     
and tc_simple_tm_nf tm =
  match tm with
  | VarT id -> tc_ok (VarT id)
  | DefAppT (id, args) ->
     tc_lookup_def id >>= fun def -> 
     (match def with
      | TCCellDef cell_tm ->
         tc_traverse (tc_simple_tm_nf) args >>= fun args_nf -> 
         tc_simple_cell_nf cell_tm >>= fun cell_nf ->
         tc_ok (CellAppT (cell_nf, args_nf))
      | TCTermDef (tele, _, term) ->
         (* The order here may be inefficient, but is currently necessary,
          * as normalization will rename all the pasting diagram variables
          * so that the names in "tele" no longer correspond correctly.
          * By first performing the substitution, we avoid this problem. 
          *)
         let sub = List.combine (List.map fst tele) args in
         let sub_tm = subst_tm sub term in
         tc_simple_tm_nf sub_tm
     )
  | CellAppT (cell, args) ->
     tc_traverse (tc_simple_tm_nf) args >>= fun args_nf -> 
     tc_simple_cell_nf cell >>= fun cell_nf ->
     tc_ok (CellAppT (cell_nf, args_nf))
     
and tc_simple_cell_nf cell =
  match cell with
  | CohT (pd, typ) ->
     tc_uniquify_pd pd >>= fun (pd_nf, s, _) ->
     tc_simple_ty_nf (subst_ty s typ) >>= fun ty_nf ->
     tc_ok (CohT (pd_nf, ty_nf))
  | CompT (pd, typ) ->
     tc_uniquify_pd pd >>= fun (pd_nf, s, _) ->
     tc_simple_ty_nf (subst_ty s typ) >>= fun ty_nf ->
     tc_ok (CompT (pd_nf, ty_nf))
                     
and tc_uniquify_pd pd =
  match pd with
  | (id, ObjT) :: [] ->
     let obj_id = "x0" in 
     tc_ok ((obj_id, ObjT)::[], (id, VarT obj_id)::[], 1)
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     tc_uniquify_pd pd' >>= fun (upd, sub, k) ->
     let tgt_id' = sprintf "x%d" k in 
     let fill_id' = sprintf "x%d" (k+1) in
     let tgt_typ' = subst_ty sub tgt_typ in
     let fill_typ' = subst_ty ((tgt_id,VarT tgt_id')::sub) fill_typ in 
     tc_ok ((fill_id', fill_typ')::(tgt_id', tgt_typ')::upd,
            (fill_id, VarT fill_id')::(tgt_id, VarT tgt_id')::sub,k+2)
  | _ -> tc_fail "Internal error: invalid pasting diagram"

(* Compare types and terms up to simple normalization *)
let tc_eq_nf_ty ty_a ty_b =
  tc_simple_ty_nf ty_a >>= fun ty_a_nf ->
  tc_simple_ty_nf ty_b >>= fun ty_b_nf ->
  tc_ok (ty_a_nf = ty_b_nf)

let tc_eq_nf_tm tm_a tm_b =
  tc_simple_tm_nf tm_a >>= fun tm_a_nf ->
  tc_simple_tm_nf tm_b >>= fun tm_b_nf ->
  tc_ok (tm_a_nf = tm_b_nf)
    
(*
 * Typechecking Internal Terms
 *)

let rec tc_check_ty t =
  match t with
  | ObjT -> tc_ok ObjT
  | ArrT (typ, src, tgt) ->
     tc_check_ty typ >>= fun typ' -> 
     tc_check_tm src typ' >>= fun src_tm ->
     tc_check_tm tgt typ' >>= fun tgt_tm -> 
     tc_ok (ArrT (typ', src_tm, tgt_tm))

and tc_check_tm tm ty =
  tc_infer_tm tm >>= fun (tm', ty') ->
  tc_simple_ty_nf ty >>= fun ty_a ->
  tc_simple_ty_nf ty' >>= fun ty_b -> 
  if (ty_a = ty_b) then tc_ok tm' else
    let msg = sprintf "The term %s was expected to have type %s,
                       but was inferred to have type %s"
                      (print_tm_term tm') (print_ty_term ty)
                      (print_ty_term ty') in
    tc_fail msg

and tc_infer_tm tm =
  match tm with
  | VarT id -> 
     tc_lookup_var id >>= fun typ ->
     tc_ok (VarT id, typ)
  | DefAppT (id, args) ->
     tc_lookup_def id >>= fun def ->
     (match def with
      | TCCellDef cell_tm -> 
         let pd = cell_pd cell_tm in
         tc_check_args args pd >>= fun sub ->
         let typ = subst_ty sub (cell_typ cell_tm) in 
         tc_ok (DefAppT (id, List.map snd sub), typ)
      | TCTermDef (tele, typ, _) -> 
         tc_check_args args tele >>= fun sub ->
         let typ' = subst_ty sub typ in
         tc_ok (DefAppT (id, List.map snd sub), typ')
     )
  | CellAppT (cell, args) ->
     tc_check_cell cell >>= fun cell_tm ->
     let pd = cell_pd cell_tm in 
     tc_check_args args pd >>= fun sub ->
     let typ = subst_ty sub (cell_typ cell_tm) in 
     tc_ok (CellAppT (cell_tm, List.map snd sub), typ)

and tc_check_ctx ctx =
  match ctx with
  | [] -> tc_ok []
  | (id,typ)::ctx' ->
     tc_check_ctx ctx' >>= fun g ->
     tc_in_ctx g (tc_check_ty typ) >>= fun typ_tm ->
     tc_ok ((id,typ_tm)::g)

and tc_check_args args ctx =
  match (args, ctx) with 
  | (_::_, []) -> tc_fail "Too many arguments!"
  | ([], _::_) -> tc_fail "Not enough arguments!"
  | ([], []) -> tc_ok []
  | (arg_tm::args', (id,arg_typ)::ctx') ->
     tc_check_args args' ctx' >>= fun sub ->
     let arg_typ' = subst_ty sub arg_typ in
     tc_check_tm arg_tm arg_typ' >>= fun arg_tm' ->
     tc_ok ((id, arg_tm') :: sub)
     
and tc_check_cell cell =
  match cell with
  | CohT (pd, typ) -> 
     tc_check_pd pd >>= fun (pd', _, _) ->
     tc_with_vars pd' (tc_check_ty typ) >>= fun typ' ->
     let pd_vars = SS.of_list (List.map fst pd') in
     let typ_vars = ty_free_vars typ' in
     if (not (SS.subset pd_vars typ_vars)) then
       tc_fail "Coherence is not algebraic"
     else tc_ok (CohT (pd', typ'))
  | CompT (_, ObjT) -> tc_fail "Composition cannot target an object"
  | CompT (pd, ArrT (_, src, tgt)) ->
     tc_check_pd pd >>= fun (pd', _, _) ->
     tc_pd_src pd' >>= fun pd_src ->
     tc_pd_tgt pd' >>= fun pd_tgt ->
     tc_with_vars pd_src (tc_infer_tm src) >>= fun (src_tm, src_typ) ->
     tc_with_vars pd_tgt (tc_infer_tm tgt) >>= fun (tgt_tm, tgt_typ) ->
     tc_eq_nf_ty src_typ tgt_typ >>= fun nf_match -> 
     if (not nf_match) then
       tc_fail "Source and target do not have the same type"
     else let pd_src_vars = SS.of_list (List.map fst pd_src) in
          let pd_tgt_vars = SS.of_list (List.map fst pd_tgt) in
          let src_vars = SS.union (tm_free_vars src_tm) (ty_free_vars src_typ) in
          let tgt_vars = SS.union (tm_free_vars tgt_tm) (ty_free_vars tgt_typ) in
          if (not (SS.subset pd_src_vars src_vars)) then
            tc_fail "Source is not algebraic"
          else if (not (SS.subset pd_tgt_vars tgt_vars)) then
            tc_fail "Target is not algebraic"
          else tc_ok (CompT (pd', ArrT (src_typ, src_tm, tgt_tm)))

and tc_check_pd pd =
  match pd with
  | [] -> tc_fail "Empty context is not a pasting diagram"
  | (id, ObjT) :: [] -> tc_ok ((id, ObjT) :: [], id, ObjT)
  | (_, _) :: [] -> tc_fail "Pasting diagram does not begin with an object"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     tc_check_pd pd'                                          >>= fun (res_pd, pid, ptyp) ->
     tc_in_ctx res_pd (tc_check_ty tgt_typ)                   >>= fun tgt_typ_tm ->
     tc_in_ctx ((tgt_id, tgt_typ_tm) :: res_pd)
               (tc_check_ty fill_typ)                         >>= fun fill_typ_tm ->
     let cvars = List.map fst res_pd in 
     let codim = (dim_of ptyp) - (dim_of tgt_typ_tm) in
     tc_tgt_of (VarT pid) ptyp codim                          >>= fun (src_tm_tm, src_typ_tm) -> 
     if (tgt_typ_tm <> src_typ_tm) then
       let msg = sprintf "Type error: %s =/= %s"
                         (print_ty_term tgt_typ_tm) (print_ty_term src_typ_tm) in
       tc_fail msg
     else if (fill_typ_tm <> ArrT (src_typ_tm, src_tm_tm, VarT tgt_id)) then
       let msg = sprintf "Type error: %s =/= %s"
                         (print_ty_term (ArrT (src_typ_tm, src_tm_tm, VarT tgt_id)))
                         (print_ty_term fill_typ_tm) in
       tc_fail msg
     else if (fill_id = tgt_id) then
       tc_fail (sprintf "Fill and target cell have the same identifier: %s" fill_id)
     else if (List.mem fill_id cvars) then
       tc_fail (sprintf "Filling identifier %s already exists" fill_id)
     else if (List.mem tgt_id cvars) then 
       tc_fail (sprintf "Target identifier %s already exists" tgt_id)
     else tc_ok ((fill_id, fill_typ_tm) :: (tgt_id, tgt_typ_tm) :: res_pd, fill_id, fill_typ_tm)

(* Return the unbiased composite of a pasting diagram *)     
let rec tc_ucomp pd =
  match pd with
  | (id, ObjT) :: [] -> tc_ok (VarT id, ObjT)
  | _ -> tc_pd_src pd >>= fun pd_src ->
         tc_pd_tgt pd >>= fun pd_tgt ->
         tc_ucomp pd_src >>= fun (uc_src, uc_typ) ->
         tc_ucomp pd_tgt >>= fun (uc_tgt, _) ->
         let next_ty = ArrT (uc_typ, uc_src, uc_tgt) in 
         tc_ok (CellAppT (CompT (pd, next_ty), id_args pd), next_ty)

(* Return the identity coherence applied to a given term *)         
let tc_tm_get_id tm =
  tc_infer_tm tm >>= fun (_, ty) ->
  let args = tm_to_disc_sub tm ty in
  let id_c = id_coh (dim_of ty) in
  tc_ok (CellAppT (id_c, args))

(* Source and target functions on terms *)
let tc_tm_src tm =
  tc_infer_tm tm >>= fun (_, typ) ->
  match typ with
  | ObjT -> tc_fail (sprintf "Term %s is an object and has no source" (print_tm_term tm))
  | ArrT (_, src_tm, _) -> tc_ok src_tm

let tc_tm_tgt tm =
  tc_infer_tm tm >>= fun (_, typ) ->
  match typ with
  | ObjT -> tc_fail (sprintf "Term %s is an object and has no target" (print_tm_term tm))
  | ArrT (_, tgt_tm, _) -> tc_ok tgt_tm

let rec tc_tm_kth_src k tm =
  if (k <= 0) then tc_ok tm
  else tc_tm_kth_src (k-1) tm >>= fun t ->
       tc_tm_src t
                         
let rec tc_tm_kth_tgt k tm =
  if (k <= 0) then tc_ok tm
  else tc_tm_kth_tgt (k-1) tm >>= fun t ->
       tc_tm_tgt t
  
(* 
 * Pruning
 *)

let tc_pd_zip_is_prunable z =
  match pd_zip_head_tm z with
  | VarT _ -> tc_ok false
  | DefAppT (_, _) -> tc_ok false  (* Could expand here ... *)
  | CellAppT (CohT (_, ArrT (_, src, tgt)), _) ->
     tc_eq_nf_tm src tgt 
  | CellAppT (_, _) -> tc_ok false

let rec tc_pd_zip_prune_to_end z typ =
  tc_try (pd_zip_next_loc_max z)
         (fun z' -> printf "Inspecting locally maximal argument %s ... " (pd_zip_head_id z');
                    tc_pd_zip_is_prunable z' >>= fun is_p ->
                    if (not is_p) then
                      (printf "Not prunable!\n";
                       tc_pd_zip_prune_to_end z' typ)
                    else
                      (printf "Pruning!\n";
                       tc_lift (pd_zip_drop z') >>= fun (zd, s) ->
                       let typ' = subst_ty s typ in 
                       tc_pd_zip_prune_to_end zd typ'))
         (fun _ -> printf "Finished pruning\n";
                   tc_ok (z, typ))

(* Okay, so this simply prunes the top level ... 
 * In principle, we could recurse above and so on, 
 * which is what we are going to want to do in what follows .... *)
  
let tc_prune tm =
  match tm with
  | CellAppT (CompT (pd, typ), args) ->
     let pd_w_args = List.combine pd args in
     tc_lift (zipper_open pd_w_args >>== 
              zipper_rightmost) >>= fun z -> 
     tc_pd_zip_prune_to_end z typ >>= fun (zp, typ') ->
     let pruned_pd_w_args = zipper_close zp in
     let (pd', args') = List.split pruned_pd_w_args in
     tc_ok (CellAppT (CompT (pd', typ'), args'))
  | _ -> tc_ok tm


     
