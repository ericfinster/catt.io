(*****************************************************************************)
(*                             Internal Examples                             *)
(*****************************************************************************)

open Pd
open Expr
open Suite
open Syntax
    
let d0 : expr disc = (Emp ,
                      VarE "x")
                     
let d1 : expr disc = (Emp
                      |> (VarE "x", VarE "y") ,
                      VarE "f")
                     
let d2 : expr disc = (Emp
                      |> (VarE "x", VarE "y")
                      |> (VarE "f", VarE "g"),
                      VarE "a")


(* A utility routine for quickly parsing pasting diagrams *)
let parse_pd pd_str =
  let lexbuf = Sedlexing.Utf8.from_string pd_str in 
  let chkpt = Parser.Incremental.id_pd
      (fst (Sedlexing.lexing_positions lexbuf)) in
  Io.parse lexbuf chkpt 

let mk_pd (pd_str : string) : nm_ict pd =
  let pd = parse_pd pd_str in
  Pd.map_pd_lf_nd pd
      ~lf:(fun nm -> (nm,Expl))
      ~nd:(fun nm -> (nm,Impl)) 


(*****************************************************************************)
(*                            Interchange Example                            *)
(*****************************************************************************)

let ich_exmp () = 

  let module Eu = ExprUtil  in 
  
  let bc = VarE "C" in 

  let m : expr disc = (Emp
                       |> (VarE "x", VarE "y")
                       |> (VarE "f", VarE "g")
                       |> (VarE "a", VarE "b"), 
                       VarE "m") in 

  let c : expr disc = (Emp
                       |> (VarE "x", VarE "y")
                       |> (VarE "g", VarE "h"),
                       VarE "c") in 

  let i : expr disc = (Emp
                       |> (VarE "y", VarE "z"),
                       VarE "i") in 

  let wh = Eu.whisker in 
  let mc : expr disc = wh bc m 1 c in 
  let mc_i : expr disc = wh bc mc 0 i in 
  
  let mi : expr disc = wh bc m 0 i in 
  let ci : expr disc = wh bc c 0 i in 
  let mi_ci : expr disc = wh bc mi 1 ci in 
  
  let base_cat : expr =
    Eu.sph_to_cat bc (fst (grab 1 (fst mi_ci))) in 
  
  let ipd : nm_ict pd =
    mk_pd "(x(f(a(m)b)g(c)h)y(i)z)" in 
  
  let src_disc : expr disc =
    (Suite.from_list (snd (grab 1 (fst mc_i))) , snd mc_i) in 
  
  let tgt_disc : expr disc = 
    (Suite.from_list (snd (grab 1 (fst mi_ci))) , snd mi_ci) in 
  
  let (cyl_ty,cyl_tm) =
    Cylinder.ExprCylCoh.cylcoh_impl ("C", Impl)
      ipd base_cat src_disc tgt_disc in

  log_val "cyl_ty" cyl_ty pp_expr;
  log_val "cyl_tm" cyl_tm pp_expr;

  let open Typecheck in

  let m =
    let (let*) m f = Base.Result.bind m ~f in
    log_msg "Checking cylinder coherence type validity ...";
    let* cyl_typ_tm = check empty_ctx cyl_ty TypV in
    let cyl_typ_v = Eval.eval Emp Emp cyl_typ_tm in
    log_msg "Checking cylinder coherence validity ...";
    let* _ = check empty_ctx cyl_tm cyl_typ_v in Ok () 
    
  in run_tc m; 
  log_msg "Finished"


let assoc_exmp () =

  let bc = VarE "C" in 
  
  let m = (Emp
           |> (VarE "x", VarE "y")
           |> (VarE "f", VarE "g")
           |> (VarE "a", VarE "b"), 
           VarE "m") in 

  let n = (Emp
           |> (VarE "y", VarE "z")
           |> (VarE "h", VarE "i")
           |> (VarE "c", VarE "d"), 
           VarE "n") in 

  let o = (Emp
           |> (VarE "z", VarE "w")
           |> (VarE "j", VarE "k")
           |> (VarE "s", VarE "t"), 
           VarE "o") in 

  let wh = ExprUtil.whisker in 
  let r = wh bc m 0 (wh bc n 0 o) in
  let l = wh bc (wh bc m 0 n) 0 o in

  let apd = mk_pd "(x(f(a(m)b)g)y(h(c(n)d)i)z(j(s(o)t)k)w)" in
  
  let (cyl_ty,cyl_tm) =
    Cylinder.ExprCylCoh.cylcoh_impl ("C", Impl)
      apd bc r l in

  log_val "cyl_ty" cyl_ty pp_expr;
  log_val "cyl_tm" cyl_tm pp_expr;
  
  let open Typecheck in

  let m =
    let (let*) m f = Base.Result.bind m ~f in
    log_msg "Checking cylinder coherence type validity ...";
    let* cyl_typ_tm = check empty_ctx cyl_ty TypV in
    let cyl_typ_v = Eval.eval Emp Emp cyl_typ_tm in
    log_msg "Checking cylinder coherence validity ...";
    let* _ = check empty_ctx cyl_tm cyl_typ_v in Ok () 
    
  in run_tc m; 
  log_msg "Finished"

  
(*****************************************************************************)
(*                             Strengthening Test                            *)
(*****************************************************************************)
    
open Term

let ucomp_sph (pd : 'a pd) : term sph =
  match term_ucomp pd with
  | CohT (_,_,c,s,t) ->
    snd (TermUtil.match_homs (HomT (c,s,t)))
  | _ -> failwith "unexpected"

let rec test_term_strengthen (pd : 'a pd) (sph : term sph) =
  let st = TermPdUtil.strengthen in 
  let dim = Suite.length sph - 1 in 
  match sph with
  | Emp -> log_msg "Starting test ..."
  | Ext (sph',(s,t)) ->

    log_val "s" s pp_term;
    let src_tm = st true dim pd s in
    log_val "src_tm" src_tm pp_term;

    log_val "t" t pp_term;
    let tgt_tm = st false dim pd t in
    log_val "tgt_tm" tgt_tm pp_term;
    
    test_term_strengthen pd sph'

let do_test pd =
  test_term_strengthen pd (ucomp_sph pd)

let coh_pd =
  mk_pd "(x(f(a(m)b)g(c)h)y(i)z)"

let gen_sub src dim pd =

  let bpd = Pd.truncate src dim pd in
  let blvl = pd_length bpd in 

  log_msg "--------------";
  log_val "pd" pd Pd.pp_tr;
  log_val "bpd" bpd Pd.pp_tr;
  log_val "blvl" blvl Fmt.int;

  let sub = Pd.fold_pd_with_type pd (Ext (Emp, ("C",Some (VarT blvl))) , blvl - 1)
      (fun x ty (s,i) ->
         let incld = (Ext (s,(x,Some (VarT i))),i-1) in 
         let excld = (Ext (s,(x,None)),i) in
         match ty with
         | SrcCell d ->
           if src then 
             (if (d > dim) then excld else incld)
           else
             (if (d < dim) then incld else excld)
         | TgtCell d ->
           if src then 
             (if (d < dim) then incld else excld)
           else
             (if (d > dim) then excld else incld)
         | IntCell d ->
           if (d < dim) then incld else excld
         | LocMaxCell d ->
           if (d <= dim) then incld else excld
      )

  in

  log_val "sub" (map_suite (fst sub) ~f:snd)
    (pp_suite (Fmt.option ~none:(Fmt.any "*") pp_term));
  log_msg "--------------";

  sub
