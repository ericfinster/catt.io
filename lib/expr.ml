(*****************************************************************************)
(*                                                                           *)
(*                           User Level Expressions                          *)
(*                                                                           *)
(*****************************************************************************)

open Pd
open Term
open Suite

open Format

(*****************************************************************************)
(*                                Expressions                                *)
(*****************************************************************************)
    
type ty_expr =
  | ObjE
  | ArrE of tm_expr * tm_expr

 and tm_expr =
   | VarE of string
   | CohE of tele * ty_expr * tm_expr suite
   | DefAppE of string * tm_expr suite

 and tele = (string * ty_expr) suite

(*****************************************************************************)
(*                            Printing Expressions                           *)
(*****************************************************************************)
     
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
    fprintf ppf "@[<hov>%s(%a)@]"
      id (pp_print_suite_horiz pp_print_expr_tm) args
  | CohE (tele, typ, args) ->
    fprintf ppf "@[<hov>coh[%a : %a](%a)@]"
      (pp_print_tele) tele
      pp_print_expr_ty typ
      (pp_print_suite_horiz pp_print_expr_tm) args

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
(*                            From Internal Terms                            *)
(*****************************************************************************)

let rec term_to_expr_ty f ty =
  match ty with
  | ObjT -> ObjE
  | ArrT (_,src,tgt) ->
    ArrE (term_to_expr_tm f src,
          term_to_expr_tm f tgt)

and term_to_expr_tm f tm =
  match tm with
  | VarT i -> f i 
  | DefAppT (id,args) ->
    DefAppE (id,map (term_to_expr_tm f) args)
  | CohT (pd,typ,args) ->
    let args' =
      (match args_to_pd pd args with
       | Ok pd_args -> leaves pd_args
       | Fail _ -> args) in
    CohE (map (fun (i,t) -> (Printf.sprintf "x%d" i, term_to_expr_ty f t))
            (zip_with_idx (pd_to_ctx pd)),
          term_to_expr_ty f typ,
          map (term_to_expr_tm f) args')

let term_to_expr_ty_default ty =
  term_to_expr_ty
    (fun i -> VarE (Printf.sprintf "x%d" i)) ty
  
let term_to_expr_tm_default tm =
  term_to_expr_tm
    (fun i -> VarE (Printf.sprintf "x%d" i)) tm
