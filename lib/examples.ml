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
