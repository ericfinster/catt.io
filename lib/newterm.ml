(*
 * newterm.ml - internal term representation
 *)

type 'a dyck =
  | Pt of 'a
  | Up of 'a * 'a * 'a dyck
  | Down of 'a dyck

type pd = unit dyck
type lpd = string dyck
    
type ty_term =
  | ObjT
  | ArrT of ty_term * tm_term * tm_term
          
 and tm_term =
   | VarT of int
   | DefAppT of tm_term list
   | CellAppT of cell_term * tm_term list

 and cell_term =
   | CohT of pd * ty_term
   | CompT of pd * ty_term   

