(*****************************************************************************)
(*                                                                           *)
(*                        Internal Term Representation                       *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Pd
open Suite

open Mtl

module StringErr =
  ErrMnd(struct type t = string end)

open MonadSyntax(StringErr) 

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

(* This is a bit of an orphan and should probably
   go somewhere else ... *)
let err_lookup_var i l =
  try Ok (nth i l)
  with Not_found -> Fail (sprintf "Unknown index: %d" i)

(* map the given arguments into the 
   pasting diagram *)
let args_to_pd pd args =
  let module PdT = PdTraverse(MndToApp(StringErr)) in 
  let get_arg t =
    match t with
    | VarT i -> err_lookup_var i args
    | _ -> Fail "Invalid term in pasting diagram"
  in PdT.traverse get_arg pd

      
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
  let* (unit_pd,_,_,_,_) = ctx_to_unit_pd gma in
  Ok (pd_to_db unit_pd)

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
    
