(*
 * pd.ml - routines on pasting diagrams
 *)

open Term

type 'a pd =
  | ObjP of 'a 
  | UpP of 'a * 'a * ('a pd)
  | DownP of 'a pd

type spd = string pd

(* Return the assoc list determined by a pasting diagram *)    
(* let rec to_ctx pd =
 *   match pd with
 *   | ObjP id -> ((id, ObjT)::[] , VarT id , ObjT)
 *   | UpP (fill_id, tgt_id, tl) ->
 *     let (tl', src, ty) = to_ctx tl in
 *     let ty' = ArrT (ty, src, VarT tgt_id) in 
 *     ((fill_id, ty')::(tgt_id, ty)::tl',
 *      VarT fill_id,
 *      ty')
 *   (\* Ummm.  Pass to target of the returned type? *\)
 *   | DownP tl -> to_ctx tl  *)


