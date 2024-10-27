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
type 'a g_diagram = (sub * 'a tele * sub) pd 

let g_limit (d : 'a g_diagram) (gma : 'a tele) : 'a tele =
  match d with
  | Br ((lsub,ctx,rsub),brs) ->

    
    failwith "not done" 

type computope = term sph 
type pointed_computope = computope * term 

let rec realize (c : computope) : (sub * term tele * term) sph =
  match c with 
  | Emp -> Emp
  | Ext (c',(s,t)) ->

    let bdry = realize c in 

    
    failwith "not done"

let realize_term (bdry : (sub * term tele * term) sph) (t : term) : term =
  match t with
  | CVarT ->
    
    begin match bdry with
      | Emp -> failwith "" 
      | Ext (bdry',((_,s_ctx,s_tm),(_,t_ctx,t_tm))) ->

        


        failwith ""
    end
      
  | CohT (pd,c,s,t) ->
    failwith "a coherence cell"


  | _ -> failwith "not a computopic term" 
                                              
    
