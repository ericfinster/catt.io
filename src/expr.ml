(*
 * expr.ml - user-level expressions
 *)

open Term
open Typecheck
open Normalization
open Printf
   
(* User Expressions *)
type ty_expr =
  | ObjE
  | ArrE of tm_expr * tm_expr

 and tm_expr =
   | VarE of string
   | DefAppE of string * tm_expr list
   | CellAppE of cell_expr * tm_expr list

 and cell_expr =
   | CohE of tele * ty_expr
   | CompE of tele * ty_expr

 and tele = (string * ty_expr) list

(* Printing expressions *)    
let rec print_ty_expr t =
  match t with
  | ObjE -> "*"
  | ArrE (src, tgt) -> 
     sprintf "%s -> %s" (print_tm_expr src) (print_tm_expr tgt)
    
and print_tm_expr t =
  let print_args args =
    String.concat ", " (List.map print_tm_expr (List.rev args)) in 
  match t with
  | VarE id -> id
  | DefAppE (id, args) ->
     sprintf "%s(%s)" id (print_args args)
  | CellAppE (cell, args) -> 
     sprintf "[%s](%s)" (print_cell_expr cell) (print_args args)
             
and print_cell_expr t =
  let print_decl = fun (id, typ) ->
    sprintf "(%s : %s)" id (print_ty_expr typ) in 
  let print_pd pd =
    String.concat " " (List.map print_decl (List.rev pd)) in 
  match t with
  | CohE (pd, typ) ->
     sprintf "coh %s : %s" (print_pd pd) (print_ty_expr typ)
  | CompE (pd, typ) ->
     sprintf "comp %s : %s" (print_pd pd) (print_ty_expr typ)

let print_expr_ctx g =
  let print_decl = fun (id, typ) ->
    sprintf "(%s : %s)" id (print_ty_expr typ) in 
  let decls = List.map print_decl g in
  String.concat " " (List.rev decls)
    
(*
 * Typechecking User Expressions
 *)

let rec tc_check_ty_expr t =
  match t with
  | ObjE -> tc_ok ObjT
  | ArrE (src, tgt) ->
     tc_infer_tm_expr src >>= fun (src_tm, src_ty) ->
     tc_infer_tm_expr tgt >>= fun (tgt_tm, tgt_ty) ->
     tc_eq_nf_ty src_ty tgt_ty >>= fun nf_match -> 
     if (nf_match) then 
       tc_ok (ArrT (src_ty, src_tm, tgt_tm))
     else let msg = sprintf "%s =/= %s when checking that an arrow 
                             type is well-formed."
                            (print_tm_term src_tm) (print_tm_term tgt_tm) in 
          tc_fail msg

and tc_check_tm_expr tm ty =
  tc_infer_tm_expr tm >>= fun (tm', ty') ->
  tc_eq_nf_ty ty ty' >>= fun nf_match -> 
  if (nf_match) then tc_ok tm' else
    let msg = sprintf "The term %s was expected to have type %s,
                       but was inferred to have type %s"
                      (print_tm_term tm') (print_ty_term ty)
                      (print_ty_term ty') in
    tc_fail msg

and tc_infer_tm_expr tm =
  match tm with
  | VarE id -> 
     tc_lookup_var id >>= fun typ ->
     tc_ok (VarT id, typ)
  | DefAppE (id, args) ->
     tc_lookup_def id >>= fun def ->
     (match def with
      | TCCellDef cell_tm -> 
         (* printf "Cell %s has definition %s\n" id (print_cell_term cell_tm); *)
         let pd = cell_pd cell_tm in
         tc_check_args_expr args pd >>= fun sub ->
         let typ = subst_ty sub (cell_typ cell_tm) in 
         tc_ok (DefAppT (id, List.map snd sub), typ)
      | TCTermDef (tele, typ, _) -> 
         tc_check_args_expr args tele >>= fun sub ->
         let typ' = subst_ty sub typ in
         tc_ok (DefAppT (id, List.map snd sub), typ')
     )
  | CellAppE (cell, args) ->
     tc_check_cell_expr cell >>= fun cell_tm ->
     let pd = cell_pd cell_tm in 
     tc_check_args_expr args pd >>= fun sub ->
     let typ = subst_ty sub (cell_typ cell_tm) in 
     tc_ok (CellAppT (cell_tm, List.map snd sub), typ)

and tc_check_tele tele =
  match tele with
  | [] -> tc_ok []
  | (id,typ)::tele' ->
     tc_check_tele tele' >>= fun g ->
     tc_in_ctx g (tc_check_ty_expr typ) >>= fun typ_tm ->
     tc_ok ((id,typ_tm)::g)

and tc_check_args_expr args tele =
  match (args, tele) with 
  | (_::_, []) -> tc_fail "Too many arguments!"
  | ([], _::_) -> tc_fail "Not enough arguments!"
  | ([], []) -> tc_ok []
  | (arg_exp::args', (id,arg_typ)::tele') ->
     tc_check_args_expr args' tele' >>= fun sub ->
     let arg_typ' = subst_ty sub arg_typ in
     tc_check_tm_expr arg_exp arg_typ' >>= fun arg_tm ->
     tc_ok ((id, arg_tm) :: sub)
     
and tc_check_cell_expr cell =
  match cell with
  | CohE (pd, typ) -> 
     tc_check_pd_expr pd >>= fun (pd', _, _) ->
     printf "Valid pasting diagram: %s\n" (print_term_ctx pd');
     tc_with_vars pd' (tc_check_ty_expr typ) >>= fun typ' ->
     let pd_vars = SS.of_list (List.map fst pd') in
     let typ_vars = ty_free_vars typ' in
     if (not (SS.subset pd_vars typ_vars)) then
       tc_fail "Coherence is not algebraic"
     else tc_ok (CohT (pd', typ'))
  | CompE (_, ObjE) -> tc_fail "Composition cannot target an object"
  | CompE (pd, ArrE (src, tgt)) ->
     tc_check_pd_expr pd >>= fun (pd', _, _) ->
     printf "Valid pasting diagram: %s\n" (print_term_ctx pd');
     tc_pd_src pd' >>= fun pd_src ->
     printf "Source diagram: %s\n" (print_term_ctx pd_src);
     tc_pd_tgt pd' >>= fun pd_tgt ->
     printf "Target diagram: %s\n" (print_term_ctx pd_tgt);
     tc_with_vars pd_src (tc_infer_tm_expr src) >>= fun (src_tm, src_typ) ->
     printf "Source term is: %s\n" (print_tm_term src_tm); 
     tc_with_vars pd_tgt (tc_infer_tm_expr tgt) >>= fun (tgt_tm, tgt_typ) ->
     printf "Target term is: %s\n" (print_tm_term tgt_tm); 
     if (src_typ <> tgt_typ) then
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
                                      
(* Okay, here we need to generate a "standard form" for the variables
 * in a pasting diagram.  This is because we will need to compare them
 * during typing, and this has to be up to alpha equivalence.  I guess
 * indices would normally be the solution to this problem, but it turns
 * out that this makes calculating sources and targets *really* painful.
 *)                    
and tc_check_pd_expr pd =
  match pd with
  | [] -> tc_fail "Empty context is not a pasting diagram"
  | (id, ObjE) :: [] -> tc_ok ((id, ObjT) :: [], id, ObjT)
  | (_, _) :: [] -> tc_fail "Pasting diagram does not begin with an object"
  | (fill_id, fill_typ) :: (tgt_id, tgt_typ) :: pd' ->
     tc_check_pd_expr pd'                                          >>= fun (res_pd, pid, ptyp) ->
     tc_in_ctx res_pd (tc_check_ty_expr tgt_typ)                   >>= fun tgt_typ_tm ->
     tc_in_ctx ((tgt_id, tgt_typ_tm) :: res_pd)
               (tc_check_ty_expr fill_typ)                         >>= fun fill_typ_tm ->
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


(* Commands *)
type cmd =
  | CellDef of string * cell_expr
  | TermDef of string * tele * ty_expr * tm_expr
  | EqNf of tele * tm_expr * tm_expr
  | LocMax of tele
     
(*
 *  Top-level command execution
 *)
                   
let rec check_cmds cmds =
  match cmds with
  | [] -> tc_ok ()
  | (CellDef (id, cell)) :: ds ->
     printf "-----------------\n";
     printf "Checking cell: %s\n" id;
     tc_check_cell_expr cell >>= fun cell_tm ->
     printf "Ok!\n";
     tc_with_cell id cell_tm (check_cmds ds)
  | (TermDef (id, tele, typ, tm)) :: ds ->
     printf "-----------------\n";
     printf "Checking definition: %s\n" id;
     tc_check_tele tele >>= fun g ->
     printf "Valid telescope: %s\n" (print_term_ctx g);
     tc_in_ctx g (tc_check_ty_expr typ) >>= fun typ_tm ->
     printf "Valid return type: %s\n" (print_ty_term typ_tm);
     tc_in_ctx g (tc_check_tm_expr tm typ_tm) >>= fun tm_tm ->
     printf "Valid definition: %s\n" (print_tm_term tm_tm);
     tc_with_def id g typ_tm tm_tm (check_cmds ds)
  | (EqNf (tele, tm_a, tm_b) :: ds) ->
     printf "-----------------\n";
     printf "Comparing normal forms\n";
     tc_check_tele tele >>= fun g ->
     printf "Valid telescope: %s\n" (print_term_ctx g);
     tc_in_ctx g (tc_infer_tm_expr tm_a) >>= fun (tm_a_tm, tm_a_ty) ->
     printf "Term %s has type %s\n" (print_tm_term tm_a_tm) (print_ty_term tm_a_ty);
     tc_in_ctx g (tc_infer_tm_expr tm_b) >>= fun (tm_b_tm, tm_b_ty) ->
     printf "Term %s has type %s\n" (print_tm_term tm_b_tm) (print_ty_term tm_b_ty);
     if (tm_a_tm = tm_b_tm) then
       printf "Match!\n"
     else printf "Fail!\n";
     check_cmds ds
  | (LocMax tele :: ds) ->
     printf "-----------------\n";
     printf "Locally maximal variables\n";
     tc_check_pd_expr tele >>= fun (pd, _, _) ->
     List.iter (printf "%s ") (locally_maximal pd);
     printf "\n";
     check_cmds ds
          
