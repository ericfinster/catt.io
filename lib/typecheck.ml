(*
 * typecheck.ml - catt typechecker
 *)

open Common
open Printf
open Term

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
let tc_get_env env = Succeed env
let tc_with_env env m _ = m env
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
  | (id, ObjT) :: [] ->
     if (k >= 0) then
       tc_ok ((id, ObjT) :: [])
     else tc_ok []
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
  | (id, ObjT) :: [] ->
     if (k >= 0) then
       tc_ok ((id, ObjT) :: [])
     else tc_ok []
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

let rec tc_traverse_with_int f xs n =
  match xs with
  | [] -> tc_ok ([], n)
  | x :: xs -> f x n >>= fun (y, k) ->
               tc_traverse_with_int f xs k >>= fun (ys, k') ->
               tc_ok (y :: ys, k')



(* Basic normalization (unfold definitions, uniquify pd's *)
let rec tc_simple_ty_nf ty n =
  match ty with
  | ObjT -> tc_ok (ObjT, n)
  | ArrT (ty', src, tgt) ->
     tc_simple_ty_nf ty' n >>= fun (ty_nf, k) ->
     tc_simple_tm_nf src k >>= fun (src_nf, k1) ->
     tc_simple_tm_nf tgt k1 >>= fun (tgt_nf, k2) ->
     tc_ok (ArrT (ty_nf, src_nf, tgt_nf), k2)

and tc_simple_tm_nf tm n =
  match tm with
  | VarT id -> tc_ok (VarT id, n)
  | DefAppT (id, args) ->
     tc_lookup_def id >>= fun def ->
     (match def with
      | TCCellDef cell_tm ->
         tc_traverse_with_int tc_simple_tm_nf args n >>= fun (args_nf, k) ->
         tc_simple_cell_nf cell_tm k >>= fun (cell_nf, k1) ->
         tc_ok (CellAppT (cell_nf, args_nf), k1)
      | TCTermDef (tele, _, term) ->
         (* The order here may be inefficient, but is currently necessary,
          * as normalization will rename all the pasting diagram variables
          * so that the names in "tele" no longer correspond correctly.
          * By first performing the substitution, we avoid this problem.
          *)
         let sub = List.combine (List.map fst tele) args in
         let sub_tm = subst_tm sub term in
         tc_simple_tm_nf sub_tm n
     )
  | CellAppT (cell, args) ->
     tc_traverse_with_int tc_simple_tm_nf args n >>= fun (args_nf, k) ->
     tc_simple_cell_nf cell k >>= fun (cell_nf, k1) ->
     tc_ok (CellAppT (cell_nf, args_nf), k1)

and tc_simple_cell_nf cell n =
  match cell with
  | CohT (pd, typ) ->
     tc_uniquify_pd pd n >>= fun (pd_nf, s, k) ->
     tc_simple_ty_nf (subst_ty s typ) k >>= fun (ty_nf, k1) ->
     tc_ok (CohT (pd_nf, ty_nf), k1)
  | CompT (pd, typ) ->
     tc_uniquify_pd pd n >>= fun (pd_nf, s, k) ->
     tc_simple_ty_nf (subst_ty s typ) k >>= fun (ty_nf, k1) ->
     tc_ok (CompT (pd_nf, ty_nf), k1)

and tc_uniquify_pd pd n =
  match pd with
  | (id, ObjT) :: [] ->
     let obj_id = sprintf "x%d" n in
     tc_ok ((obj_id, ObjT)::[], (id, VarT obj_id)::[], n + 1)
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     tc_uniquify_pd pd' n >>= fun (upd, sub, k) ->
     let tgt_id' = sprintf "x%d" k in
     let fill_id' = sprintf "x%d" (k+1) in
     let tgt_typ' = subst_ty sub tgt_typ in
     let fill_typ' = subst_ty ((tgt_id,VarT tgt_id')::sub) fill_typ in
     tc_ok ((fill_id', fill_typ')::(tgt_id', tgt_typ')::upd,
            (fill_id, VarT fill_id')::(tgt_id, VarT tgt_id')::sub,k+2)
  | _ -> tc_fail "Internal error: invalid pasting diagram"

(* Compare types and terms up to simple normalization *)
let tc_eq_nf_ty ty_a ty_b =
  tc_simple_ty_nf ty_a 0 >>= fun (ty_a_nf, _) ->
  tc_simple_ty_nf ty_b 0 >>= fun (ty_b_nf, _) ->
  tc_ok (ty_a_nf = ty_b_nf)

let tc_eq_nf_tm tm_a tm_b =
  tc_simple_tm_nf tm_a 0 >>= fun (tm_a_nf, _) ->
  tc_simple_tm_nf tm_b 0 >>= fun (tm_b_nf, _) ->
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
  tc_simple_ty_nf ty 0 >>= fun (ty_a, _) ->
  tc_simple_ty_nf ty' 0 >>= fun (ty_b, _) ->
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
  tc_try (is_disc_pd pd)
         (fun (id, ty) -> tc_ok (VarT id, ty))
         (fun _ -> tc_pd_src pd >>= fun pd_src ->
                   tc_pd_tgt pd >>= fun pd_tgt ->
                   tc_ucomp pd_src >>= fun (uc_src, uc_typ) ->
                   tc_ucomp pd_tgt >>= fun (uc_tgt, _) ->
                   let next_ty = ArrT (uc_typ, uc_src, uc_tgt) in
                   tc_ok (CellAppT (CompT (pd, next_ty), id_args pd), next_ty))

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

let rec tc_app_zip_prune_to_end z typ =
  tc_try (app_zip_next_loc_max z)
         (fun z' -> (* printf "Inspecting locally maximal argument %s ... " (app_zip_head_id z'); *)
                    match app_zip_head_tm z' with
                    | CellAppT (cell, _) ->
                       tc_try (is_identity_coh cell)
                              (fun _ -> (* printf "Pruning identity coherence.\n";
                                        printf "Term was: %s\n" (print_tm_term (app_zip_head_tm z')); *)
                                        tc_lift (app_zip_drop z') >>= fun (zd, s) ->
                                        let typ' = subst_ty s typ in
                                        tc_app_zip_prune_to_end zd typ')
                              (fun _ -> (* printf "Not an identity coherence.\n"; *)
                                        tc_app_zip_prune_to_end z' typ)
                    | _ -> (* printf "Not a cell application.\n"; *)
                           tc_app_zip_prune_to_end z' typ)
         (fun _ -> (* printf "Finished pruning\n"; *)
                   tc_ok (z, typ))

let rec tc_prune_cell pd typ args =
  let pd_w_args = List.combine pd args in
  tc_lift (zipper_open_right pd_w_args) >>= fun z ->
  tc_app_zip_prune_to_end z typ >>= fun (zp, typ') ->
  let pruned_pd_w_args = zipper_close zp in
  let (pd', args') = List.split pruned_pd_w_args in
  (* If a non-trivial pruning occurred, we may have introduced
   * new redexes.  So continue until we stabilize ... *)
  if (List.length pd' < List.length pd) then
    tc_prune_cell pd' typ' args'
  else tc_ok (pd', typ', args')
  (* tc_ok (pd', typ', args') *)


(* We prune coherences.  Is this legit? *)
let tc_prune tm =
  match tm with
  | CellAppT (CompT (pd, typ), args) ->
     tc_prune_cell pd typ args >>= fun (pd', typ', args') ->
     tc_ok (CellAppT (CompT (pd', typ'), args'))
  | CellAppT (CohT (pd, typ), args) ->
     tc_prune_cell pd typ args >>= fun (pd', typ', args') ->
     tc_ok (CellAppT (CohT (pd', typ'), args'))
  | _ -> tc_ok tm

(*
 * Rectification
 *)

let tc_rectify tm =
  (* printf "Rectifying term: %s\n" (print_tm_term tm); *)
  match tm with
  | CellAppT (cell, args) ->
     tc_try (is_unary_comp cell)
            (* Is it really the head, or the last element? *)
            (fun _ -> (* printf "Got a unary composite!\n";  *)
                      let arg = List.hd args in
                      (* printf "Head term is: %s\n" (print_tm_term arg); *)
                      tc_ok arg)
            (fun _ -> tc_try (is_endomorphism_coh cell)
                             (fun (pd, tm, ty) ->
                               (* printf "Got an endo-coherence!\n"; *)
                               (* printf "Term: %s\n" (print_tm_term tm); *)
                               (* We want to return the identity coherence on
                                * this term after substituting the arguments. *)
                               let sub = List.combine (List.map fst pd) args in
                               let tm' = subst_tm sub tm in
                               let ty' = subst_ty sub ty in
                               let id_args = tm_to_disc_sub tm' ty' in
                               let id_coh = id_coh (dim_of ty') in
                               let result = CellAppT (id_coh, id_args) in
                               (* printf "Result: %s\n" (print_tm_term result); *)
                               tc_ok result)
                             (fun _ -> tc_ok tm))
  | _ -> tc_ok tm

(*
 * Full Normalization (assumes cell is already simply normalized ...)
 *)

let rec tc_full_normalize_ty ty =
  match ty with
  | ObjT -> tc_ok ObjT
  | ArrT (typ, src, tgt) ->
     tc_full_normalize_ty typ >>= fun typ_nf ->
     tc_full_normalize_tm src >>= fun src_nf ->
     tc_full_normalize_tm tgt >>= fun tgt_nf ->
     tc_ok (ArrT (typ_nf, src_nf, tgt_nf))

and tc_full_normalize_tm tm =
  match tm with
  | VarT id -> tc_ok (VarT id)
  | DefAppT (_, _) -> tc_fail "can't normalize a def"
  | CellAppT (CompT (pd, typ), args) ->
     (* printf "Pruning composition cell: %s\n" (print_cell_term (CompT (pd, typ))); *)
     (* printf "Arguments are: %s\n" (print_sub (List.combine (List.map fst pd) args)); *)
     tc_traverse (tc_full_normalize_tm) args >>= fun args_nf ->
     (* tc_full_normalize_ty typ >>= fun typ_nf -> *)
     (* printf "Fully-normalized type: %s\n" (print_ty_term typ_nf); *)
     tc_prune_cell pd typ args_nf >>= fun (pd', typ', args') ->
     tc_full_normalize_ty typ' >>= fun typ_nf ->
     (* printf "Fully-normalized type: %s\n" (print_ty_term typ_nf); *)
     tc_rectify (CellAppT (CompT (pd', typ_nf), args'))
  | CellAppT (CohT (pd, typ), args) ->
     (* printf "Pruning coherence cell: %s\n" (print_cell_term (CohT (pd, typ))); *)
     tc_traverse (tc_full_normalize_tm) args >>= fun args_nf ->
     (* tc_full_normalize_ty typ >>= fun typ_nf -> *)
     tc_prune_cell pd typ args_nf >>= fun (pd', typ', args') ->
     tc_full_normalize_ty typ' >>= fun typ_nf ->
     tc_rectify (CellAppT (CohT (pd', typ_nf), args'))

(*
 * Normalizers and promotions
 *)

let tc_invert_coh tm =
  match tm with
  | CellAppT(CohT(pd,ArrT(typ,src,tgt)),args) ->
     tc_ok (CellAppT(CohT(pd,ArrT(typ,tgt,src)),args))
  | _ -> tc_fail "Not a coherence"

(* We suppose that u and v are parallel and that *)
(*    f "extends" u' -> v' *)
let rec tc_promote pd btyp u v ftyp f =
  printf "Attempting to promote: %s\n" (print_tm_term f);
  printf "u = %s\n" (print_tm_term u);
  printf "v = %s\n" (print_tm_term v);
  match btyp with
  | ObjT -> tc_ok (f,ftyp)
  | ArrT (btyp', su, tu) ->
    tc_promote pd btyp' su tu ftyp f >>= fun (fp, fp_typ) ->
    let k = dim_of btyp in
    let n = dim_of ftyp in
    let codim = n - k in
    tc_lift (pad_pd (k+1) n) >>= fun ppd ->
    tc_ucomp ppd >>= fun (pcoh, _) ->
    (* Which pd to use here? *)
    tc_pd_kth_src codim pd >>= fun u_pd ->
    tc_pd_kth_tgt codim pd >>= fun v_pd ->
    tc_normalizer u_pd u btyp >>= fun (pu, pu_typ) ->
    tc_normalizer v_pd v btyp >>= fun (pv, pv_typ) ->
    tc_invert_coh pv >>= fun pv_inv ->
    let lm_args = [(pv_inv,opposite pv_typ);(fp,fp_typ);(pu,pu_typ)] in
    (* let lm_args = [(pv,pv_typ);(fp,fp_typ);(pu,pu_typ)] in  *)
    tc_lift (pd_zip_expand_args ppd lm_args) >>= fun args ->
    match pcoh with
    | CellAppT (cell, _) ->
       let result = CellAppT (cell, args) in
       let pd = cell_pd cell in
       let sub = List.combine (List.map fst pd) args in
       let result_typ = subst_ty sub (cell_typ cell) in
       (* printf "Finished promotion with: %s\n" (print_tm_term result); *)
       tc_ok (result, result_typ)
    | _ -> tc_fail "internal error"


  (* | CellAppT (cell, args) -> *)
  (*    tc_check_cell cell >>= fun cell_tm -> *)
  (*    let pd = cell_pd cell_tm in  *)
  (*    tc_check_args args pd >>= fun sub -> *)
  (*    let typ = subst_ty sub (cell_typ cell_tm) in  *)
  (*    tc_ok (CellAppT (cell_tm, List.map snd sub), typ) *)

(* In principle, we do not actually need to normalize the
 * term here, as the normalization should have been available
 * above directly from the type of f....
 *)
and tc_normalizer pd tm typ =
  tc_full_normalize_tm tm >>= fun tm' ->
  match typ with
  | ObjT -> let args = tm_to_disc_sub tm typ in
            let id_c = id_coh (dim_of typ) in
            tc_ok (CellAppT (id_c, args), ArrT (ObjT,tm,tm))
  | ArrT (typ',s,t) ->
     tc_promote pd typ' s t typ tm' >>= fun (promo, _) ->
     let nmlzr = CellAppT (CohT (pd, ArrT(typ,tm,promo)),
                           (List.map (fun (id, _) -> VarT id) pd)) in
     let nmlzr_typ = ArrT (typ,tm,promo) in
     tc_ok (nmlzr, nmlzr_typ)
