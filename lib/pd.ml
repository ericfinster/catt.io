(*****************************************************************************)
(*                                                                           *)
(*                               Batanin Trees                               *)
(*                                                                           *)
(*****************************************************************************)

open Suite

(* Monadic bind for errors in scope *)
let (let*) m f = Base.Result.bind m ~f 

type 'a pd =
  | Br of 'a * ('a * 'a pd) suite

let is_leaf pd = 
  match pd with
  | Br (_,Emp) -> true
  | _ -> false
    
let rec dim_pd pd =
  match pd with
  | Br (_,brs) ->
    let f d (_,b) = max d (dim_pd b) in 
    1 + fold_left f (-1) brs 

let rec is_disc pd =
  match pd with
  | Br (_,Emp) -> true
  | Br (_,Ext(Emp,(_,pd'))) -> is_disc pd'
  | _ -> false

let rec shape_eq pd_a pd_b =
  match (pd_a,pd_b) with
  | (Br (_,brs_a),Br (_,brs_b)) ->
    try fold2 brs_a brs_b true
          (fun b (_,br_a) (_,br_b) ->
             b && shape_eq br_a br_b)
    with Failure _ -> false 

(* Truncate to the provided dimension.  The boolean
   flag dir is true for the source direction, false
   for the target *)

let rec truncate dir d pd =
  match pd with
  | Br (a, brs) ->
    if (d <= 0) then
      (
        if dir then Br (a, Emp)
        else let a' = fold_left (fun _ (y,_) -> y) a brs in 
          Br (a', Emp)
      )
    else Br (a, map_suite brs ~f:(fun (l,b) -> (l,truncate dir (d-1) b)))

let boundary pd =
  let d = dim_pd pd in
  let r = range 0 (d-1) in
  map_suite r
    ~f:(fun i -> (truncate true i pd,
                  truncate false i pd))
      
let rec append_leaves pd lvs =
  match pd with
  | Br (l,Emp) -> Ext (lvs,l)
  | Br (_,bs) -> 
    let open SuiteMnd in
    bs >>= (fun (_,b) -> leaves b)

and leaves pd = append_leaves pd Emp

let rec labels pd =
  match pd with
  | Br (l,brs) ->
    let open SuiteMnd in
    append (singleton l)
      (brs >>= (fun (bl,b) -> append (singleton bl) (labels b)))

let label_of pd =
  match pd with
  | Br (a,_) -> a
    
let with_label a pd =
  match pd with
  | Br(_, brs) -> Br (a,brs)

(* The addresses of a source and target are
   the same in this implementation. A more subtle
   version would distinguish the two .... *)
      
let rec zip_with_addr_lcl addr pd =
  match pd with
  | Br (l,brs) ->
    let brs' = map_suite (zip_with_idx brs)
        ~f:(fun (i,(x,b)) ->
            let addr' = Ext (addr,i) in 
            ((addr',x),zip_with_addr_lcl addr' b))
    in Br ((addr,l),brs')

let zip_with_addr pd =
  zip_with_addr_lcl Emp pd
  
(*****************************************************************************)
(*                             Discs and Spheres                             *)
(*****************************************************************************)

type 'a sph = ('a * 'a) suite
type 'a disc = 'a sph * 'a 

type 'a lsph = ('a * 'a) list
type 'a ldisc = 'a lsph * 'a 

let map_sph sph ~f =
  map_suite sph ~f:(fun (s,t) -> (f s, f t))
    
let map_disc (sph,d) ~f =
  (map_sph sph ~f , f d)

let pp_sph pp_el ppf sph =
  let open Fmt in
  pf ppf "@[<hov>%a@]" (pp_suite ~sep:(sps 1 ++ any "| ")
                 (hovbox (pair ~sep:(any " =>" ++ sps 1) pp_el pp_el))) sph

let pp_disc pp_el ppf (sph, flr) =
  let open Fmt in
  if (is_empty sph) then
    pf ppf "%a" pp_el flr
  else
    pf ppf "@[%a | %a@]" (pp_sph pp_el)
      sph pp_el flr

let rec nth_target (sph,d) n =
  if (n <= 0) then (sph,d)
  else match sph with
    | Emp -> failwith "No Target"
    | Ext (sph',(_,t)) ->
      nth_target (sph',t) (n-1)

let rec nth_source (sph,d) n =
  if (n <= 0) then (sph,d)
  else match sph with
    | Emp -> failwith "No Source"
    | Ext (sph',(s,_)) ->
      nth_source (sph',s) (n-1)

(*****************************************************************************)
(*                                   Zipper                                  *)
(*****************************************************************************)

type 'a pd_ctx = 'a * 'a * ('a * 'a pd) suite * ('a * 'a pd) list 
type 'a pd_zip = 'a pd_ctx suite * 'a pd

let visit d (ctx, fcs) =
  match fcs with
  | Br (s,brs) ->
    let* (l,(t,b),r) = open_at d brs in
    Ok (Ext (ctx,(s,t,l,r)), b)

let rec seek addr pz =
  match addr with
  | Emp -> Ok pz
  | Ext(addr',d) ->
    let* pz' = seek addr' pz in
    visit d pz'

let rec addr_of (ctx, fcs) =
  match ctx with
  | Emp -> Emp
  | Ext(ctx',(s,t,l,r)) ->
    Ext (addr_of (ctx', Br (s, close (l,(t,fcs),r))), length l)

let rec pd_close (ctx, fcs) =
  match ctx with
  | Emp -> fcs
  | Ext(ctx',(s,t,l,r)) ->
    pd_close (ctx', Br (s, close (l,(t,fcs),r)))

let pd_drop (ctx, _) =
  match ctx with
  | Emp -> Error "Cannot drop root"
  | Ext(ctx',(s,_,l,r)) ->
    Ok (ctx', Br(s, append_list l r))

let parent (ctx,fcs) =
  match ctx with
  | Emp -> Error "No parent in empty context"
  | Ext(ctx',(s,t,l,r)) ->
    Ok (ctx', Br (s, close (l,(t,fcs),r)))

let sibling_right (ctx,fcs) =
  match ctx with
  | Ext(ctx',(s,t,l,(t',fcs')::rs)) ->
    Ok (Ext (ctx',(s,t',Ext (l,(t,fcs)),rs)), fcs')
  | _ -> Error "No right sibling"

let sibling_left (ctx,fcs) =
  match ctx with
  | Ext(ctx',(s,t,Ext(l,(t',fcs')),r)) ->
    Ok (Ext (ctx',(s,t',l,(t,fcs)::r)), fcs')
  | _ -> Error "No left sibling"

let rec to_rightmost_leaf (ctx,fcs) =
  match fcs with
  | Br (_,Emp) -> Ok (ctx, fcs)
  | Br (s,Ext(brs,(t,b))) ->
    to_rightmost_leaf
      (Ext (ctx,(s,t,brs,[])), b)

let rec to_leftmost_leaf (ctx,fcs) =
  match fcs with
  | Br (_,Emp) -> Ok (ctx, fcs)
  | Br (s,brs) ->
    let* (_,(t,b),r) = open_leftmost brs in
    to_leftmost_leaf
      (Ext(ctx,(s,t,Emp,r)),b)

let (<||>) m n = if (Base.Result.is_ok m) then m else n 
    
let rec parent_sibling_left z =
  let open Base.Result.Monad_infix in 
  sibling_left z <||>
  (parent z >>= parent_sibling_left) <||>
  Error "No more left siblings"

let rec parent_sibling_right z =
  let open Base.Result.Monad_infix in 
  sibling_right z <||>
  (parent z >>= parent_sibling_right) <||>
  Error "No more right siblings"

let leaf_right z =
  let open Base.Result.Monad_infix in 
  parent_sibling_right z >>=
  to_leftmost_leaf

let leaf_left z =
  let open Base.Result.Monad_infix in 
  parent_sibling_left z >>=
  to_rightmost_leaf

let insert_at ?before:(bf=true) addr b pd =
  match addr with
  | Emp -> Error "Empty address for insertion"
  | Ext(base,dir) ->
    let* (ctx, fcs) = seek base (Emp, pd) in 
    let* newfcs =
      (match fcs with
       | Br (a,brs) ->
         let* (l,br,r) = open_at dir brs in
         if bf then 
           Ok (Br (a, close (l,b,br::r)))
         else
           Ok (Br (a, close (Ext (l,br),b,r)))) in 
    Ok (pd_close (ctx, newfcs))

(*****************************************************************************)
(*                          Left and Right Insertion                         *)
(*****************************************************************************)

let rec insert_right pd d lbl nbr =
  match pd with
  | Br (a,brs) ->
    if (d <= 0) then
      Ok (Br (a, Ext(brs,(lbl,nbr))))
    else match brs with
      | Emp -> Error "Depth overflow"
      | Ext(bs,(b,br)) ->
        let* rbr = insert_right br (d-1) lbl nbr in 
        Ok (Br (a,Ext(bs,(b,rbr))))

let insert_left pd d lbl nbr =
  let addr = repeat (d+1) 0 in
  insert_at addr (lbl,nbr) pd 
  
(*****************************************************************************)
(*                                Custom Maps                                *)
(*****************************************************************************)

let rec map_pd pd ~f =
  match pd with
  | Br (a, brs) ->
    let fm (l, b) = (f l, map_pd b ~f:f) in
    Br (f a, map_suite brs ~f:fm)

let fold_pd_lf_nd pd init ~lf ~nd =

  let rec fold_pd_lf_nd_br acc br =
    match br with
    | Br (x,brs) ->
      let acc' =
        if (is_empty brs) then
          lf acc x
        else nd acc x
      in fold_pd_lf_nd_brs acc' brs

  and fold_pd_lf_nd_brs acc brs =
    match brs with
    | Emp -> acc
    | Ext (brs',(x,br)) ->
      let acc' = fold_pd_lf_nd_brs acc brs' in
      let acc'' = nd acc' x in 
      fold_pd_lf_nd_br acc'' br 

  in fold_pd_lf_nd_br init pd

let fold_pd pd init ~f =
  fold_pd_lf_nd pd init ~lf:f ~nd:f
    
let map_pd_lf_nd_lvl pd ~lf ~nd =

  let rec map_pd_lf_nd_lvl_br k br =
    match br with
    | Br (x,brs) ->
      let x' =
        if (is_empty brs) then
          lf k x
        else nd k x in
      let (k',brs') = map_pd_lf_nd_lvl_brs (k+1) brs in
      (k',Br (x',brs'))

  and map_pd_lf_nd_lvl_brs k brs =
    match brs with
    | Emp -> (k,Emp)
    | Ext (brs',(x,br)) ->
      let (k',brs'') = map_pd_lf_nd_lvl_brs k brs' in
      let x' = nd k' x in 
      let (k'',br') = map_pd_lf_nd_lvl_br (k'+1) br in
      (k'',Ext (brs'',(x',br')))

  in snd (map_pd_lf_nd_lvl_br 1 pd)


let map_pd_lvls (pd : 'a pd) (init : int)
    ~f:(f : int -> int -> bool -> 'a -> 'b) : 'b pd =

  let k = length (labels pd) in
  
  let rec pd_info_br l br =
    match br with
    | Br (x,brs) ->
      let x' = f k l (is_empty brs) x in
      let (brs',l') = pd_info_brs (l+1) brs in
      (Br (x',brs'), l')


  and pd_info_brs l brs =
    match brs with
    | Emp -> (Emp,l)
    | Ext (brs',(x,br)) ->
      let (brs'',l') = pd_info_brs l brs' in
      let x' = f k l' false x in
      let (br',l'') = pd_info_br (l'+1) br in
      (Ext (brs'',(x',br')) , l'')

  in fst (pd_info_br init pd)

(* Map over the pasting diagram with 
   the boundary sphere of labels in context *)
    
let map_with_sph pd f =
  
  let rec map_with_disc_br sph br =
    match br with
    | Br (src,brs) ->
      let r = f sph src in
      let (brs',tgt) = map_with_disc_brs sph src brs in
      (Br (r,brs'), tgt)

  and map_with_disc_brs sph src brs =
    match brs with
    | Emp -> (Emp, src)
    | Ext (brs',(tgt,br)) ->
      let (brs'',src') = map_with_disc_brs sph src brs' in
      let r = f sph tgt in 
      let (br',_) = map_with_disc_br (Ext (sph,(src',tgt))) br in 
      (Ext (brs'',(r,br')),tgt)

  in fst (map_with_disc_br Emp pd)

(* Fold with the sphere in context, as well as leaf information *)
let fold_left_with_sph pd f b =
  
  let rec fold_left_with_disc_br sph br b =
    match br with
    | Br (src,brs) ->
      let b' = f sph src b (is_empty brs) in
      fold_left_with_disc_brs sph src brs b' 

  and fold_left_with_disc_brs sph src brs b =
    match brs with
    | Emp -> (b, src)
    | Ext (brs',(tgt,br)) ->
      let (b',src') = fold_left_with_disc_brs sph src brs' b in
      let b'' = f sph tgt b' false in 
      let (b''',_) = fold_left_with_disc_br (Ext (sph,(src',tgt))) br b'' in
      (b''',tgt)

  in fst (fold_left_with_disc_br Emp pd b)

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let rec pp_pd f ppf pd =
  match pd with
  | Br (s,brs) ->
    let pp_pair ppf (x,br) =
      Fmt.pf ppf "%a%a" (pp_pd f) br f x in 
    Fmt.pf ppf "(%a%a)" f s
      (pp_suite ~sep:Fmt.nop pp_pair) brs

(* a simple parenthetic representation of a pasting diagram *)
let rec pp_tr ppf pd =
  match pd with
  | Br (_,brs) ->
    Fmt.pf ppf "%a" (Fmt.parens (pp_suite ~sep:Fmt.nop pp_tr))
      (map_suite brs ~f:snd)

(*****************************************************************************)
(*                              Pd Construction                              *)
(*****************************************************************************)

let rec disc_pd_inverted (b,f) =
  match b with
  | [] -> Br (f, Emp)
  | (s,t)::b' ->
    Br (s, Ext (Emp, (t, disc_pd_inverted (b',f))))

let disc_pd (bdry,flr) =
  disc_pd_inverted (to_list bdry, flr)
    
let unit_disc n =
  (repeat n ((),()), ())
  
let unit_disc_pd n =
  disc_pd (unit_disc n)

let whisk_left (bdry,flr) i pd =
  let cobdry = Base.List.drop (to_list bdry) i in
  match cobdry with
  | [] -> Error "invalid whiskering"
  | (_,t)::c' ->
    insert_left pd i t (disc_pd_inverted (c',flr))

let whisk_right pd i (bdry,flr) =
  let cobdry = Base.List.drop (to_list bdry) i in
  match cobdry with
  | [] -> Error "invalid whiskering"
  | (_,t)::c' ->
    insert_right pd i t (disc_pd_inverted (c',flr))

let three_disc = ([("a","b");("c","d");("e","f")],"g")
let two_disc = ([("0","1");("2","3")],"4")
      
let rec comp_seq s =
  match s with
  | [] -> failwith "Invalid Comp Seq"
  | n::[] -> unit_disc_pd n
  | n::i::s' ->
    Base.Result.ok_or_failwith
      (whisk_left (unit_disc n) i (comp_seq s'))

let whisk m i n = comp_seq [m;i;n]

(*****************************************************************************)
(*                      Substitution of Pasting Diagrams                     *)
(*****************************************************************************)

let rec merge d p q =
  match p,q with
  | Br (l,bas), Br (_,bbs) ->
    if (d <= 0) then
      Br (l, append bas bbs)
    else
      let mm ((l,p'),(_,q')) = (l,merge (d-1) p' q') in 
      Br (l, map_suite (zip bas bbs) ~f:mm)

let rec join_pd d pd =
  match pd with
  | Br (p,brs) ->
    let jr (_,b) = join_pd (d+1) b in
    fold_left (merge d) p (map_suite brs ~f:jr)

let blank pd = map_pd pd ~f:(fun _ -> ()) 
let subst pd sub = map_pd pd ~f:(fun id -> Suite.assoc id sub) 
         
(*****************************************************************************)
(*                                  Examples                                 *)
(*****************************************************************************)

let obj = Br ("x", Emp)
    
let arr = Br ("x", Emp
                   |> ("y", Br ("f", Emp)))

let mk_obj x = Br (x, Emp)
let mk_arr x y f = Br (x,Emp
                         |> (y, Br (f, Emp)))

let twodisc = Br ("x", Emp
                       |> ("y", Br ("f", Emp
                                         |> ("g", Br ("a", Emp)))))

let threedisc = Br ("x", Emp
                         |> ("y", Br ("f", Emp
                                           |> ("g", Br ("a", Emp
                                                             |> ("b", Br ("m", Emp)))))))

let comp2 = Br ("x", Emp
                     |> ("y", Br ("f", Emp))
                     |> ("z", Br ("g", Emp)))
    
let comp3 = Br ("x", Emp
                     |> ("y", Br ("f", Emp))
                     |> ("z", Br ("g", Emp))
                     |> ("w", Br ("h", Emp)))

let vert2 = Br ("x", Emp
                     |> ("y", Br ("f", Emp
                                       |> ("g", Br ("a", Emp))
                                       |> ("h", Br ("b", Emp)))))

let horiz2 = Br ("x", Emp
                      |> ("y", Br ("f", Emp
                                        |> ("g", Br ("a", Emp))))
                      |> ("z", Br ("h", Emp
                                        |> ("k", Br ("b", Emp)))))

let ichg = Br ("x", Emp
                    |> ("y", Br ("f", Emp
                                      |> ("g", Br ("a", Emp))
                                      |> ("h", Br ("b", Emp))))
                    |> ("z", Br ("i", Emp
                                      |> ("j", Br ("c", Emp))
                                      |> ("k", Br ("d", Emp)))))

let vert2whiskl = Br ("x", Emp
                           |> ("y", Br ("f", Emp
                                             |> ("g", Br ("a", Emp))
                                             |> ("h", Br ("b", Emp))))
                           |> ("z", Br ("k", Emp)))

let disc2 = Br ("x", Emp
                     |> ("y", Br ("f", Emp
                                       |> ("g", Br ("a", Emp)))))

let ichgmidwhisk =  Br ("x", Emp
                             |> ("y", Br ("f", Emp
                                               |> ("g", Br ("a", Emp))
                                               |> ("h", Br ("b", Emp))))
                             |> ("z", Br ("i", Emp))
                             |> ("w", Br ("j", Emp
                                               |> ("k", Br ("c", Emp))
                                               |> ("l", Br ("d", Emp)))))

(*****************************************************************************)
(*                           Substitution Examples                           *)
(*****************************************************************************)
    
let example =
  subst comp2
    (Emp
     |> ("x", obj)
     |> ("y", obj)
     |> ("z", obj)
     |> ("f", comp2)
     |> ("g", comp2))

let example2 =
  subst vert2
    (Emp
     |> ("x" , obj)
     |> ("y" , obj)
     |> ("f" , comp2)
     |> ("g" , comp2)
     |> ("h" , comp2)
     |> ("a" , horiz2)
     |> ("b" , horiz2))

let example3 =
  subst ichgmidwhisk
    (Emp
     |> ("x", obj)
     |> ("y", obj)
     |> ("f", comp2)
     |> ("g", comp2)
     |> ("a", vert2whiskl)
     |> ("h", comp2)
     |> ("b", ichg)
     |> ("z", obj)
     |> ("i", comp3)
     |> ("w", obj)
     |> ("j", arr)
     |> ("k", arr)
     |> ("c", disc2)
     |> ("l", arr)
     |> ("d", vert2))

let example4 =
  subst arr
    (Emp
     |> ("x", Br("x",Emp))
     |> ("y", Br("z",Emp))
     |> ("f", comp2))

let example5 =
  subst comp2
    (Emp
     |> ("x", mk_obj "x")
     |> ("y", mk_obj "y")
     |> ("f", mk_arr "x" "y" "f")
     |> ("z", mk_obj "z")
     |> ("g", mk_arr "y" "z" "g"))


