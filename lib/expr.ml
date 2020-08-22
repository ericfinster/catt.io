(*****************************************************************************)
(*                                                                           *)
(*                           User Level Expressions                          *)
(*                                                                           *)
(*****************************************************************************)

open Term
open Suite
    
type ty_expr =
  | ObjE
  | ArrE of tm_expr * tm_expr

 and tm_expr =
   | VarE of string
   | CohE of tele * ty_expr * tm_expr suite
   | DefAppE of string * tm_expr suite

 and tele = (string * ty_expr) suite

(*****************************************************************************)
(*                             Printing Raw Terms                            *)
(*****************************************************************************)

open Format

let rec pp_print_expr_ty ppf ty =
  match ty with
  | ObjE -> fprintf ppf "*"
  | ArrE (src, tgt) ->
    fprintf ppf "%a -> %a"
      pp_print_expr_tm src
      pp_print_expr_tm tgt
              
and pp_print_expr_tm ppf tm =
  match tm with
  | VarE id -> fprintf ppf "%s" id
  | DefAppE (id, args) ->
    fprintf ppf "%s(%a)"
      id (pp_print_suite pp_print_expr_tm) args
  | CohE (tele, typ, args) ->
    fprintf ppf "coh[%a : %a](%a)"
      (pp_print_tele) tele
      pp_print_expr_ty typ
      (pp_print_suite pp_print_expr_tm) args

and pp_print_tele ppf tele =
  match tele with
  | Emp -> ()
  | Ext(tele',(id,ty)) ->
    fprintf ppf "%a(%s : %a)@ "
      pp_print_tele tele'
      id (pp_print_expr_ty) ty

let expr_ty_to_str ty =
  pp_print_expr_ty str_formatter ty;
  flush_str_formatter ()

let expr_tm_to_str tm = 
  pp_print_expr_tm str_formatter tm;
  flush_str_formatter ()

let expr_tele_to_str tele =
  pp_print_tele str_formatter tele;
  flush_str_formatter ()
    
(*****************************************************************************)
(*                        Typechecking Raw Expressions                       *)
(*****************************************************************************)

open TcMonad
open TcMonad.MonadSyntax

let rec expr_tc_check_ty typ = 
    
  match typ with
  | ObjE -> tc_ok ObjT
  | ArrE (src, tgt) -> 
    let* (src_tm, src_ty) = expr_tc_infer_tm src in
    let* (tgt_tm, tgt_ty) = expr_tc_infer_tm tgt in

    let* _ = catch (tc_eq_nf_ty src_ty tgt_ty) 

      (fun _ -> let msg = asprintf "%a =/= %a when checking that %a is a valid type"
                    pp_print_ty src_ty
                    pp_print_ty tgt_ty
                    pp_print_expr_ty typ
        in tc_fail msg) in 
    
    tc_ok (ArrT (src_ty, src_tm, tgt_tm))

and expr_tc_check_tm tm ty =
  
  let* (tm', ty') = expr_tc_infer_tm tm in
  let* _ = catch (tc_eq_nf_ty ty ty')

      (fun _ -> let msg = asprintf "%a =/= %a when inferring the type of %a"
                    pp_print_ty ty
                    pp_print_ty ty'
                    pp_print_expr_tm tm
        in tc_fail msg) in 

  tc_ok tm'
  
and expr_tc_infer_tm tm = 

  match tm with
  
  | VarE id ->
    let* l = tc_id_to_level id in
    (* let* d = tc_depth in
     * let k = d - l - 1 in  *)
    let* typ = tc_lookup_var l in

    printf "Looking up id: %s@," id;
    printf "Result type: %a@," pp_print_ty typ;
    
    tc_ok (VarT l, typ)

  | DefAppE (id, args) -> (
    let* def = tc_lookup_def id in
    match def with
    | TCCellDef (pd,typ) -> 
      let pd_ctx = pd_to_ctx pd in
      let* args' = expr_tc_check_args args pd_ctx in
      tc_ok (DefAppT (id, args'), subst_ty args' typ)
    | TCTermDef (gma, typ, _) -> 
      let* args' = expr_tc_check_args args gma in
      tc_ok (DefAppT (id, args'), subst_ty args' typ)
  )

  | CohE (tele, typ, args) ->
    let* (gma, pd, typ') = expr_tc_check_coh tele typ in
    let* args' = expr_tc_check_args args gma in
    tc_ok (CohT (pd,typ',args'), subst_ty args' typ')
    
and expr_tc_check_args sub gma =
  match (sub,gma) with
  | (Ext (_,_), Emp) -> tc_fail "Too many arguments!"
  | (Emp, Ext (_,_)) -> tc_fail "Not enough arguments!"
  | (Emp, Emp) -> tc_ok Emp
  | (Ext (sub',tm), Ext (gma',typ)) ->
    let* rsub = expr_tc_check_args sub' gma' in
    let typ' = subst_ty rsub typ in
    let* rtm = expr_tc_check_tm tm typ' in
    tc_ok (Ext (rsub, rtm))

(* run the computation m in the context given 
 * by the telescope, checking as one goes that
 * the telescope is valid *)
      
and expr_tc_in_tele tele m =
  match tele with
  | Emp ->
    let* env = tc_env in
    tc_with_env { gma = Emp ; rho = env.rho ; tau = Emp } m 
  | Ext (tele',(id,typ)) -> 
    expr_tc_in_tele tele'
      (let* typ' = expr_tc_check_ty typ in
       let* env = tc_env in
       let* d = tc_depth in 
       let env' = {
         gma = Ext (env.gma, typ');
         rho = env.rho;
         tau = Ext (env.tau, (id,d))
       } in 
       tc_with_env env' m)
    
and expr_tc_check_coh tele typ =
  expr_tc_in_tele tele
    (let* typ' = expr_tc_check_ty typ in
     let* gma = tc_ctx in
     printf "Telescope: %a@," pp_print_ctx gma;
     let* pd = tc_lift (ctx_to_pd gma) in
     let* _ = tc_check_is_full pd typ' in
     tc_ok (gma, pd, typ'))


