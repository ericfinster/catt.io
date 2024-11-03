(*****************************************************************************)
(*                                                                           *)
(*                             Computopes                                    *)
(*                                                                           *)
(*****************************************************************************)

open Suite
open Syntax
open Term 
open Pd

(*****************************************************************************)
(*                           Globular Limits                                 *)
(*****************************************************************************)

type sub = idx suite 
type 'a globular_diagram = (sub * 'a tele * sub) pd 

let compose (s : sub) (t : sub) : sub =
  map_suite s ~f:(fun i -> db_get i t) 

let globular_limit (d : term globular_diagram) : sub pd * term tele =
  failwith "in progress"


(*****************************************************************************)
(*                       Realization of Computopes                           *) 
(*****************************************************************************)

let rec app_to_sub (tm : term) : term * term suite =
  match tm with
  | AppT (f,a,_) ->
    let (stem,sub) = app_to_sub f in 
    (stem,Ext(sub,a)) 
  | _ -> (tm,Emp) 

let realize_term (tm : term) (ty : term) : (sub * term) sph * term tele * term =
  let (stem,sub) = app_to_sub tm in 
  match stem with
  | CVarT ->
    failwith "a cvar"
  | CohT (pd,c,s,t) ->
    failwith "a coherence cell"
  | _ -> failwith "not a computope"


    
