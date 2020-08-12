(*****************************************************************************)
(*                                                                           *)
(*                              Raw Expressions                              *)
(*                                                                           *)
(*****************************************************************************)

open Pd
open Newterm

type ty_expr =
  | ObjE
  | ArrE of tm_expr * tm_expr

 and tm_expr =
   | VarE of string
   | CohE of tele * ty_expr * tm_expr list
   | DefAppE of string * tm_expr list

 and tele = (string * ty_expr) list

(*****************************************************************************)
(*                        Typechecking Raw Expressions                       *)
(*****************************************************************************)

(* open TcMonad *)
open TcMonad.MonadSyntax

let rec tc_expr_check_ty typ =
  match typ with
  | ObjE -> tc_ok ObjT
  | ArrE (src, tgt) -> 
    let* (src_tm, src_ty) = tc_expr_infer_tm src in
    let* (tgt_tm, tgt_ty) = tc_expr_infer_tm tgt in
    (* Add a proper message here ... *)
    let* _ = tc_eq_nf_ty src_ty tgt_ty in
    tc_ok (ArrT (src_ty, src_tm, tgt_tm))

and tc_expr_check_tm tm ty =
  
  let* (tm', ty') = tc_expr_infer_tm tm in
  let* _ = tc_eq_nf_ty ty ty' in
  (* Add a proper message here ... *)
  tc_ok (tm' , ty')
  
and tc_expr_infer_tm tm =

  match tm with
  
  | VarE id ->
    let* l = tc_id_to_level id in
    let* d = tc_depth in
    let k = d - l - 1 in 
    let* typ = tc_lookup_var k in
    tc_ok (VarT k, typ)

  | DefAppE (_, _) -> tc_fail "unimplemented"

  | CohE (_, _, _) -> tc_fail "unimplemented"

(* First step: check that the context is indeed a pasting diagram ... *)

and tc_expr_check_pd ctx =
  match ctx with
  | [] -> tc_fail "Empty context is not a pasting diagram"
  | (id, ObjE) :: [] -> tc_ok (Br (id,[]), id, ObjT)            
  | (_, _) :: [] -> tc_fail "Pasting diagram does not begin with an object"
  | _ :: _ :: _ -> tc_fail "unimplemented"
  (* | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' -> 
   *   
   *   let* (res_pd, pid, ptyp) = tc_expr_check_pd pd' in
   * 
   *   
   *   (\* checking here seems redundant: the type are completely forced
   *    * by what comes before ... *\)
   *   let* tgt_typ_tm = tc_in_ctx res_pd (tc_check_ty_expr tgt_typ) in
   *   let* fill_typ_tm = tc_in_ctx ((tgt_id, tgt_typ_tm) :: res_pd)
   *       (tc_check_ty_expr fill_typ)  in
   *   
   *   let cvars = List.map fst res_pd in 
   *   let codim = (dim_of ptyp) - (dim_of tgt_typ_tm) in
   *   let* (src_tm_tm, src_typ_tm) = tc_tgt_of (VarT pid) ptyp codim in
   * 
   *   let* _ = ensure (tgt_typ_tm = src_typ_tm)
   *       (sprintf "Type error: %s =/= %s"
   *          (print_ty_term tgt_typ_tm)
   *          (print_ty_term src_typ_tm)) in
   * 
   *   let* _ = ensure (fill_typ_tm = ArrT (src_typ_tm, src_tm_tm, VarT tgt_id))
   *       (sprintf "Type error: %s =/= %s"
   *          (print_ty_term (ArrT (src_typ_tm, src_tm_tm, VarT tgt_id)))
   *          (print_ty_term fill_typ_tm)) in
   * 
   *   let* _ = ensure (fill_id <> tgt_id)
   *       (sprintf "Fill and target cell have the same identifier: %s" fill_id) in
   * 
   *   let* _ = ensure (not (List.mem fill_id cvars))
   *       (sprintf "Filling identifier %s already exists" fill_id) in 
   * 
   *   let* _ = ensure (not (List.mem tgt_id cvars))
   *       (sprintf "Target identifier %s already exists" tgt_id) in 
   * 
   *   tc_ok ((fill_id, fill_typ_tm) :: (tgt_id, tgt_typ_tm) :: res_pd, fill_id, fill_typ_tm) *)
  

(* run the computation m in the context given 
 * by the telescope, checking as one goes that
 * the telescope is valid *)
and tc_expr_check_tele tele m =
  match tele with
  | [] ->
    let* env = tc_env in
    tc_with_env { gma = [] ; rho = env.rho ; tau = [] } m
  | (id,typ)::tele' ->
    tc_expr_check_tele tele'
      (let* typ' = tc_expr_check_ty typ in
       let* env = tc_env in
       let* d = tc_depth in 
       let env' = {
         gma = typ' :: env.gma;
         rho = env.rho;
         tau = (id,d) :: env.tau
       } in 
       tc_with_env env' m)
    


