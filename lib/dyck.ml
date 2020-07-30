(*****************************************************************************)
(*                      Dyck Words and Pasting Diagrams                      *)
(*****************************************************************************)

type 'a dyck =
  | Pt of 'a
  | Up of 'a * 'a * 'a dyck
  | Down of 'a dyck

type pd = unit dyck
type lpd = string dyck
    
let rec dyck_valid_with_height d =
  match d with
  | Pt _ -> (true , 0)
  | Up (_ , _ , d) ->
    let (v , h) = dyck_valid_with_height d in
    (v && (h >= 0) , h + 1)
  | Down d -> 
    let (v , h) = dyck_valid_with_height d in
    (v && (h > 0) , h - 1)

let dyck_valid d =
  fst (dyck_valid_with_height d)

let dyck_height d =
  snd (dyck_valid_with_height d)
