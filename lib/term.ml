(*****************************************************************************)
(*                                                                           *)
(*                        Internal Term Representation                       *)
(*                                                                           *)
(*****************************************************************************)

open Pd
open Suite
    
open Cheshire.Err
open Cheshire.Monad

open Format

(*****************************************************************************)
(*                                   Terms                                   *)
(*****************************************************************************)
    
type ty_term =
  | ObjT
  | ArrT of ty_term * tm_term * tm_term
          
 and tm_term =
   | VarT of int
   | DefAppT of string * tm_term suite
   | CohT of tm_term pd * ty_term * tm_term suite

let rec map_ty f ty =
  match ty with
  | ObjT -> ObjT
  | ArrT (typ,src,tgt) ->
    let typ' = map_ty f typ in 
    let src' = map_tm f src in 
    let tgt' = map_tm f tgt in 
    ArrT (typ',src',tgt')

and map_tm f tm =
  match tm with
  | VarT i -> VarT (f i)
  | DefAppT (id, args) ->
    DefAppT (id, map (map_tm f) args)
  | CohT (pd, typ, args) ->
    CohT (pd, typ, map (map_tm f) args)

let rec dim_typ typ =
  match typ with
  | ObjT -> 0
  | ArrT (typ',_,_) -> 1 + dim_typ typ'

let rec nth_tgt n typ tm =
  if (n <= 0) then Ok (typ, tm) else
    match typ with
    | ObjT -> Fail "Target of object"
    | ArrT (typ',_,tgt) -> nth_tgt (n-1) typ' tgt

let rec nth_src n typ tm = 
  if (n <= 0) then Ok (typ, tm) else
    match typ with
    | ObjT -> Fail "Target of object"
    | ArrT (typ',src,_) -> nth_src (n-1) typ' src

(* Enclose the given pasting diagram of terms
 * with the boundaries specified by the given type *)
let rec suspend_with ty pd =
  match ty with
  | ObjT -> pd
  | ArrT (typ, src, tgt) ->
    suspend_with typ (Br (src, singleton (tgt,pd)))

(* Return the term-labelled pasting diagram 
 * associated to a type/term pair *)
let disc_pd ty tm =
  suspend_with ty (Br (tm, Emp))

let disc_sub ty tm =
  labels (disc_pd ty tm)

(*****************************************************************************)
(*                             Printing Raw Terms                            *)
(*****************************************************************************)

let rec pp_print_ty ppf ty =
  match ty with
  | ObjT -> fprintf ppf "*"
  | ArrT (typ, src, tgt) ->
    fprintf ppf "%a | %a @,-> %a"
      pp_print_ty typ
      pp_print_tm src
      pp_print_tm tgt
              
and pp_print_tm ppf tm =
  match tm with
  | VarT i -> fprintf ppf "%d" i 
  | DefAppT (id, args) ->
    fprintf ppf "@[<hov>%s(%a)@]"
      id (pp_print_suite_horiz pp_print_tm) args
  | CohT (pd, typ, args) ->
    fprintf ppf "@[<hov>coh[%a @,: %a](%a)@]"
      (pp_print_pd pp_print_tm) pd
      pp_print_ty typ
      (pp_print_suite_horiz pp_print_tm) args

let pp_print_ctx ppf gma =
  pp_print_suite pp_print_ty ppf gma

let print_tm = pp_print_tm std_formatter
let print_ty = pp_print_ty std_formatter

let print_ctx gma =
  fprintf std_formatter "@[<v>%a@]"
    pp_print_ctx gma 

let pp_print_term_pd ppf pd =
  pp_print_pd pp_print_tm ppf pd
    
let print_term_pd pd =
  pp_print_term_pd std_formatter pd

let pp_print_sub ppf sub =
  fprintf ppf "@[<hov>(%a)@]"
    (pp_print_suite_horiz pp_print_tm) sub
    
(*****************************************************************************)
(*                             De Brujin Indices                             *)
(*****************************************************************************)

(* De Brujin Lifting *)
let lift_tm tm k = map_tm ((+) k) tm
let lift_ty ty k = map_ty ((+) k) ty

(* Labels a given pasting diagram with 
 * its appropriate de Bruijn levels
 *)
    
let rec pd_to_db_br k pd =
  match pd with
  | Br (_,brs) ->
    let (k', brs') = pd_to_db_brs (k+1) brs
    in (k', Br (VarT k, brs'))
    
and pd_to_db_brs k brs =
  match brs with
  | Emp -> (k,Emp)
  | Ext (bs,(_,b)) ->
    let (k', bs') = pd_to_db_brs k bs in
    let (k'', b') = pd_to_db_br (k'+1) b in 
    (k'', Ext (bs',(VarT k', b')))

let pd_to_db pd = snd (pd_to_db_br 0 pd)

(*****************************************************************************)
(*                         Context <-> Pd Conversion                         *)
(*****************************************************************************)
    
(* Convert a pasting diagram to a context. *)
let rec pd_to_ctx_br gma typ k br =
  match br with
  | Br (_,brs) ->
    pd_to_ctx_brs (Ext (gma, typ)) (VarT k) typ (k+1) brs 

and pd_to_ctx_brs gma src typ k brs =
  match brs with
  | Emp -> (gma, src, k, typ)
  | Ext (brs',(_,br)) ->
    
    let (gma',src',k',typ') = pd_to_ctx_brs gma src typ k brs' in
    
    let br_gma = Ext (gma', typ') in 
    let br_typ = ArrT (typ', src', VarT k') in

    let (gma'',_,k'',typ'') = pd_to_ctx_br br_gma br_typ (k'+1) br in
    
    match typ'' with
    | ObjT -> raise Not_found
    | ArrT (bt,_,tgt) ->
      (gma'', tgt, k'', bt)

let pd_to_ctx pd = let (rpd,_,_,_) = pd_to_ctx_br Emp ObjT 0 pd in rpd 

(* Try to convert a context to a pasting diagram *)
let rec ctx_to_unit_pd gma =
  let open ErrMonad.MonadSyntax in
  match gma with
  | Emp -> Fail "Empty context is not a pasting diagram"
  | Ext (Emp, ObjT) -> Ok (Br (VarT 0,Emp), ObjT, VarT 0, 0, 0)
  | Ext (Emp, _) -> Fail "Pasting context does not begin with an object"
  | Ext (Ext (gma', ttyp), ftyp) ->
    
    let* (pd, styp, stm, k, dim) = ctx_to_unit_pd gma' in
    
    let tdim = dim_typ ttyp in
    let codim = dim - tdim in
    
    let* (styp', stm') = nth_tgt codim styp stm in
    
    (* print_ctx gma;
     * pp_print_newline std_formatter ();
     * 
     * fprintf std_formatter "@[<v>Dim: %d@,Target dim: %d@,Source type: %a@,Source term: %a@]"
     *   dim tdim
     *   pp_print_ty styp
     *   pp_print_tm stm;
     * pp_print_newline std_formatter ();
     * 
     * fprintf std_formatter "@[<v>Extracted Source type: %a@,Extracted Source term: %a@]"
     *   pp_print_ty styp'
     *   pp_print_tm stm';
     * pp_print_newline std_formatter ();
     * 
     * pp_print_string std_formatter "************************";
     * pp_print_newline std_formatter (); *)
    
    if (styp' <> ttyp) then
      
      let msg = asprintf 
          "@[<v>Source and target types incompatible.
              @,Source: %a
              @,Target: %a@]"
          pp_print_ty styp' pp_print_ty ttyp
      in Fail msg

    else let etyp = ArrT (styp', stm', VarT (k+1)) in
      if (ftyp <> etyp) then

        let msg = asprintf
            "@[<v>Incorrect filling type.
                @,Expected: %a
                @,Provided: %a@]"
            pp_print_ty etyp
            pp_print_ty ftyp
        in Fail msg

      else let* rpd = insert pd tdim (VarT (k+1)) (Br (VarT (k+2), Emp)) in 
        Ok (rpd, ftyp, VarT (k+2), k+2, tdim+1)

let ctx_to_pd gma =
  let open ErrMonad.MonadSyntax in
  let* (unit_pd,_,_,_,_) = ctx_to_unit_pd gma in
  Ok (pd_to_db unit_pd)

(* let run_ctx_to_pd gma = 
 *   match ctx_to_unit_pd gma with
 *   | Ok (pd,_,_,_,_) -> printf "Well-formed!@,%a" (pp_print_pd pp_print_tm) pd
 *   | Fail msg -> printf "Error: %s" msg *)

(*****************************************************************************)
(*                                Substitution                               *)
(*****************************************************************************)
        
let rec subst_ty sub ty =
  match ty with
  | ObjT -> ObjT
  | ArrT (typ, src, tgt) ->
     let typ' = subst_ty sub typ in
     let src' = subst_tm sub src in
     let tgt' = subst_tm sub tgt in
     ArrT (typ', src', tgt')

and subst_tm sub tm =
  match tm with
  | VarT i -> nth i sub 
  | DefAppT (id, args) ->
     DefAppT (id, map (subst_tm sub) args)
  | CohT (pd, typ, args) ->
     CohT (pd, typ, map (subst_tm sub) args)
    
(*****************************************************************************)
(*                             Typechecking Monad                            *)
(*****************************************************************************)

type tc_def =
  | TCCohDef of tm_term pd * ty_term 
  | TCTermDef of ty_term suite * ty_term * tm_term

type tc_env = {
    gma : ty_term suite;
    rho : (string * tc_def) suite;
    tau : (string * int) suite; 
  }

let empty_env = { gma = Emp ; rho = Emp ; tau = Emp }

type 'a tcm = tc_env -> 'a err

module TcMonad = MakeMonadError(struct

    type 'a t = 'a tcm
        
    let map f m env =
      match m env with
      | Ok a -> Ok (f a)
      | Fail s -> Fail s

    let pure a _ = Ok a
        
    let bind m f env =
      match m env with
      | Fail s -> Fail s
      | Ok a -> f a env

  end)(struct

    type e = string

    let throw s _ = Fail s
    let catch m h env =
      match m env with
      | Ok a -> Ok a
      | Fail s -> h s env
        
  end)

open TcMonad
open TcMonad.MonadSyntax

let tc_ok = pure
let tc_fail = throw

let tc_in_ctx g m env = m { env with gma = g }
let tc_ctx env = Ok env.gma
let tc_env env = Ok env
let tc_with_env e m _ = m e
let tc_lift m _ = m
let tc_depth env = Ok (length env.gma)
    
let tc_with_coh id pd typ m env =
  m { env with rho = Ext (env.rho, (id, TCCohDef (pd,typ))) }
let tc_with_let id gma ty tm m env =
  m { env with rho = Ext (env.rho, (id, TCTermDef (gma,ty,tm))) }

let err_lookup_var i l =
  try Ok (nth i l)
  with Not_found -> Fail (sprintf "Unknown index: %d" i)
                      
let tc_lookup_var i env =
  err_lookup_var i env.gma

let tc_lookup_def id env =
  try Ok (assoc id env.rho)
  with Not_found -> Fail (sprintf "Unknown cell identifier: %s" id)

let tc_id_to_level id env =
  try Ok (assoc id env.tau)
  with Not_found -> Fail (sprintf "Unknown variable identifier: %s" id)

module PdT = PdTraverse(ErrMonad)
module ST = SuiteTraverse(TcMonad)

(* map the given arguments into the 
   pasting diagram *)
    
let args_to_pd pd args =
  let get_arg t =
    match t with
    | VarT i -> err_lookup_var i args
    | _ -> Fail "Invalid term in pasting diagram"
  in PdT.traverse get_arg pd

let rec tc_unfold_ty ty =
  match ty with
  | ObjT -> tc_ok ObjT
  | ArrT (typ,src,tgt) ->
    let* typ' = tc_unfold_ty typ in
    let* src' = tc_unfold_tm src in
    let* tgt' = tc_unfold_tm tgt in
    tc_ok (ArrT (typ',src',tgt'))
    
and tc_unfold_tm tm =
  match tm with
  | VarT i -> tc_ok (VarT i)
  | DefAppT (id, sub) -> (
    let* sub' = ST.traverse tc_unfold_tm sub in 
    let* def = tc_lookup_def id in
    match def with
    | TCCohDef (pd,typ) ->
      let* typ' = tc_unfold_ty typ in 
      tc_ok (CohT (pd,typ',sub'))
    | TCTermDef (_, _, tm) -> 
      tc_ok (subst_tm sub' tm)
  )
  | CohT (pd,typ,sub) ->
    let* sub' = ST.traverse tc_unfold_tm sub in
    let* typ' = tc_unfold_ty typ in 
    tc_ok (CohT (pd,typ',sub'))

(*****************************************************************************)
(*                         Strict Unit Normalization                         *)
(*****************************************************************************)

let rec id_typ k =
  if (k <= 0) then ObjT else
    ArrT (id_typ (k-1), VarT (2*k - 2), VarT (2*k - 1))

let id_cell k =
  (pd_to_db (disc k),
   ArrT (id_typ k, VarT (2*k), VarT (2*k)))
  
let identity_on ty tm =
  let (id_pd, id_ty) = id_cell (dim_typ ty) in
  CohT (id_pd, id_ty, disc_sub ty tm)

(* Extract the type of the current
   focus in a pasting diagram context *)
let rec ctx_typ ctx =
  match ctx with
  | Emp -> ObjT
  | Ext (ctx',(s,t,_,_)) ->
    ArrT (ctx_typ ctx', s, t)

(* Not used currently ... *)
let match_identity tm =
  match tm with
  | CohT (pd,typ,args) ->
    let (id_pd, id_ty) = id_cell (dim_pd pd) in
    if (pd = id_pd && typ = id_ty) then
      Ok (last args)
    else
      Fail "Not an identity"
  (* perhaps you should unfold? *)
  | _ -> Fail "Not an identity"

let is_identity tm =
  (* printf "Checking if term is ident: %a@," pp_print_tm tm; *)
  match tm with
  | CohT (pd,typ,_) ->
    (* let (id_pd,id_typ) = id_cell (dim_pd pd) in
     * printf "Expected id cell: @[<hov>%a:%a@]@," pp_print_term_pd id_pd pp_print_ty id_typ; *)
    (pd,typ)=(id_cell (dim_pd pd))
  | _ -> false

let (>>==) = ErrMonad.(>>=)
let (<||>) = ErrMonad.(<||>)

type prune_result =
  | NothingPruned
  | PrunedData of (tm_term pd * tm_term suite * tm_term suite)

(* Assumes we are at a leaf.  Finds the next
   (moving right) leaf with a prunable term
   or fails *)
let rec next_prunable z =
  (* printf "At leaf: %a@," pp_print_term_pd (snd z); *)
  if (is_identity (label_of (snd z))) then Ok z
  else leaf_right z >>==
    next_prunable

let prune_once pd =
  let open ErrMonad.MonadSyntax in 
  let* lz = to_leftmost_leaf (Emp,pd) in
  match next_prunable lz with
  | Fail _ -> Ok NothingPruned
  | Ok pz ->

    printf "Found a prunable argument: %a@," pp_print_tm (label_of (snd pz));
    
    let* (addr,dir) = (
      match addr_of pz with
      | Emp -> Fail "Invalid address during pruning"
      | Ext(a,d) -> Ok (a,d)
    ) in

    (* printf "Address: %a@," pp_print_addr (Ext(addr,dir)); *)
    
    let* dz = pd_drop pz in
    let pd' = pd_close dz in
    let db_pd = pd_to_db pd' in

    printf "New pasting diagram is: %a@," pp_print_term_pd db_pd;

    let* (ctx,fcs) = seek addr (Emp, db_pd) in

    (* printf "Seek has focus: %a@," pp_print_term_pd fcs; *)
    
    let* newfcs = 
      (match fcs with
       | Br (s,brs) ->
         let id_ty = ctx_typ ctx in
         let id_tm = identity_on id_ty s in 
         let id_br = Br (id_tm, Emp) in
         let (l,r) = split_at dir brs in
         let src = (match l with
           | Emp -> s
           | Ext(_,(t,_)) -> t) in 
         Ok (Br (s, append_list (Ext (l,(src,id_br))) r))) in

    (* printf "Got new focus@,"; *)
    
    let pi_pd = pd_close (ctx, newfcs) in 

    let pi = labels pi_pd in 
    let sigma = labels pd' in

    printf "pi: %a@," pp_print_sub pi;
    printf "sigma: %a@," pp_print_sub sigma;
    
    Ok (PrunedData (db_pd, pi, sigma))

let rec prune pd typ args =
  let open ErrMonad.MonadSyntax in 
  let* arg_pd = args_to_pd pd args in 
  let* pr = prune_once arg_pd in
  match pr with
  | NothingPruned -> Ok (pd,typ,args)
  | PrunedData (pd',pi,args') ->
    prune pd' (subst_ty pi typ) args'

let disc_cell k =
  (pd_to_db (disc k), id_typ k)

let disc_remove pd typ sub =
  (* match tm with
   * | VarT i -> Ok (VarT i)
   * | CohT (pd, typ, sub) -> *)
    if ((pd,typ) = disc_cell (dim_pd pd)) then
      Ok (last sub)
    else Ok (CohT (pd,typ,sub))
  (* | _ -> Fail "unfold in disc remove" *)

type endo_result =
  | NoEndoReduction
  | EndoReduced of tm_term

let endo_coherence tm =
  let nored = Ok NoEndoReduction in 
  match tm with
  | VarT _ -> nored
  | CohT (_, ObjT, _) -> nored
  | CohT (_, ArrT (btyp,src,tgt), sub) -> 
    if (src = tgt) then
      let src' = subst_tm sub src in
      let typ' = subst_ty sub btyp in 
      Ok (EndoReduced (identity_on typ' src'))
    else nored
  | _ -> Fail "Unfold in endo-coh"

let rec strict_unit_normalize_ty ty =
  match ty with
  | ObjT -> tc_ok ObjT
  | ArrT (typ,src,tgt) ->
    let* typ' = strict_unit_normalize_ty typ in
    let* src' = strict_unit_normalize_tm src in
    let* tgt' = strict_unit_normalize_tm tgt in 
    tc_ok (ArrT (typ',src',tgt'))

and strict_unit_normalize_tm tm =
  match tm with
  | VarT i -> tc_ok (VarT i)
  | DefAppT (id, sub) -> (
    let* def = tc_lookup_def id in
    match def with
    | TCCohDef (pd,typ) ->
      strict_unit_normalize_tm (CohT (pd,typ,sub))
    | TCTermDef (_, _, tm) -> 
      strict_unit_normalize_tm (subst_tm sub tm)
  )
  | CohT (pd,typ,sub) -> 
    let* sub' = ST.traverse strict_unit_normalize_tm sub in
    let* (ppd,ptyp,psub) = 
      if (not (is_identity tm)) then
        tc_lift (prune pd typ sub')
      else tc_ok (pd,typ,sub') in 
    let* ptyp' = strict_unit_normalize_ty ptyp in 
    let* dtm = tc_lift (disc_remove ppd ptyp' psub) in
    if (not (is_identity dtm)) then
      let* er = tc_lift (endo_coherence tm) in
      match er with
      | NoEndoReduction -> tc_ok dtm
      | EndoReduced tm' -> strict_unit_normalize_tm tm'
    else tc_ok dtm 

(*****************************************************************************)
(*                           Toplevel Normalization                          *)
(*****************************************************************************)

let tc_normalize_tm tm =
  strict_unit_normalize_tm tm 

let tc_normalize_ty ty =
  strict_unit_normalize_ty ty
    
let tc_eq_nf_ty tya tyb =
  let* tya_nf = tc_normalize_ty tya in
  let* tyb_nf = tc_normalize_ty tyb in
  if (tya_nf = tyb_nf)
  then tc_ok ()
  else tc_fail "Type mismatch"

(*****************************************************************************)
(*                                Typing Rules                               *)
(*****************************************************************************)

let rec tc_check_ty t = 
  match t with
  | ObjT -> tc_ok ObjT
  | ArrT (typ, src, tgt) ->
    let* typ' = tc_check_ty typ in
    let* src' = tc_check_tm src typ' in
    let* tgt' = tc_check_tm tgt typ' in
    tc_ok (ArrT (typ', src', tgt'))

and tc_check_tm tm ty =
  let* (tm', ty') = tc_infer_tm tm in
  let* _ = catch (tc_eq_nf_ty ty ty')

      (fun _ -> let msg = asprintf "%a =/= %a when inferring the type of %a"
                    pp_print_ty ty
                    pp_print_ty ty'
                    pp_print_tm tm
        in tc_fail msg) in 
  
  tc_ok tm'

and tc_infer_tm tm =
  match tm with
  
  | VarT i ->
    let* typ = tc_lookup_var i in
    tc_ok (VarT i , typ)
      
  | DefAppT (id, sub) -> (
    let* def = tc_lookup_def id in
    match def with
    | TCCohDef (pd,typ) -> 
      let pd_ctx = pd_to_ctx pd in
      let* sub' = tc_check_args sub pd_ctx in
      tc_ok (DefAppT (id, sub'), subst_ty sub' typ)
    | TCTermDef (ctx, typ, _) -> 
      let* sub' = tc_check_args sub ctx in
      tc_ok (DefAppT (id, sub'), subst_ty sub' typ)
  )
                      
  | CohT (pd, typ, sub) ->
    let pd_ctx = pd_to_ctx pd in
    let* typ' = tc_in_ctx pd_ctx
        (let* rtyp = tc_check_ty typ in
         tc_check_is_full pd rtyp) in 
    (* Check the substitution and calculate the return type *)
    let* sub' = tc_check_args sub pd_ctx in
    tc_ok (CohT (pd, typ', sub'), subst_ty sub' typ')

and tc_check_is_full pd typ =
  let pd_dim = dim_pd pd in
  printf "Checking fullness...";
  (* printf "Pd: %a@," (pp_print_pd pp_print_tm) pd;
   * printf "Type: @[<hov>%a@]@," pp_print_ty typ; *)
  match typ with
  | ObjT -> tc_fail "No coherences have object type."
  | ArrT (btyp,src,tgt) -> 
    let* src_pd = tc_term_pd src in
    let* tgt_pd = tc_term_pd tgt in
    let typ_dim = dim_typ btyp in
    if (typ_dim >= pd_dim) then
      let _ = () in printf "Checking coherence@,";
      let* _ = ensure (src_pd = pd) ("Non-full source in coherence") in
      let* _ = ensure (tgt_pd = pd) ("Non-full target in coherence") in
      tc_ok typ
    else
      let _ = () in printf "Checking composite@,";
      let pd_src = truncate true (pd_dim - 1) pd in
      let pd_tgt = truncate false (pd_dim - 1) pd in
      (* printf "Expected source pd: %a@," (pp_print_pd pp_print_tm) pd_src;
       * printf "Provided source pd: %a@," (pp_print_pd pp_print_tm) src_pd;
       * printf "Expected target pd: %a@," (pp_print_pd pp_print_tm) pd_tgt;
       * printf "Provided target pd: %a@," (pp_print_pd pp_print_tm) tgt_pd; *)
      let* _ = ensure (src_pd = pd_src) ("Non-full source in composite") in
      let* _ = ensure (tgt_pd = pd_tgt) ("Non-full target in composite") in 
      tc_ok typ
    
and tc_check_args sub gma =
  match (sub,gma) with
  | (Ext (_,_), Emp) -> tc_fail "Too many arguments!"
  | (Emp, Ext (_,_)) -> tc_fail "Not enough arguments!"
  | (Emp, Emp) -> tc_ok Emp
  | (Ext (sub',tm), Ext (gma',typ)) ->
    let* rsub = tc_check_args sub' gma' in
    let typ' = subst_ty rsub typ in
    let* rtm = tc_check_tm tm typ' in
    tc_ok (Ext (rsub, rtm))
    
(* Extract the pasting diagram of a well typed term.
 * Note that the term is assumed to be well typed in 
 * the current context *)
      
and tc_term_pd tm =
  match tm with
  | VarT i -> 
    let* typ = tc_lookup_var i in
    tc_ok (disc_pd typ (VarT i))
  | DefAppT (id , args) -> (
    let* def = tc_lookup_def id in
    match def with
    | TCCohDef (pd,typ) ->
      tc_term_pd (CohT (pd,typ,args))
    | TCTermDef (_, _, tm) ->
      tc_term_pd (subst_tm args tm)
  )    
  | CohT (pd, _, sub) -> 
    let* pd_sub = ST.traverse tc_term_pd sub in
    let* ppd = tc_lift (args_to_pd pd pd_sub) in
    (* printf "To Join: %a@," (pp_print_pd (pp_print_pd pp_print_tm)) ppd; *)
    let jres = join_pd 0 ppd in
    (* printf "Result: %a@," (pp_print_pd pp_print_tm) jres; *)
    tc_ok jres 
    
