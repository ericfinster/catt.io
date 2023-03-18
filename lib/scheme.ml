open Syntax
open Pd
open Value
open Suite

type coh_reduction = (string * icit) pd
                     -> int
                     -> value
                     -> value
                     -> value
                     -> (value * icit) suite
                     -> (value, string) result

module type ReductionScheme = sig
  val reductions : (string * icit) pd
                     -> int
                     -> value
                     -> value
                     -> value
                     -> (value * icit) suite
                     -> (unit -> (value, string) result) list
end
