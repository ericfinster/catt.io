(*****************************************************************************)
(*                                                                           *)
(*                              Raw Expressions                              *)
(*                                                                           *)
(*****************************************************************************)

(* open Pd *)
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

  | CohE (tele,typ, _) ->
    tc_expr_check_tele tele
      (
        let* ctx = tc_ctx in
        let* (pd,_,_,_) = tc_lift (ctx_to_pd ctx) in
        let* typ' = tc_expr_check_ty typ in
        (* Still gotta check the substitution .... *)
        tc_ok (CohT (pd,typ',[]), ObjT)
      )

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
    


