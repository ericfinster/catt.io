(*****************************************************************************)
(*                                                                           *)
(*                                Web Main                                   *)
(*                                                                           *)
(*****************************************************************************)

open Js_of_ocaml
       
open Catt.Io
open Catt.Reduction

module W = Catt.Typecheck.Make(Weak)
module SU = Catt.Typecheck.Make(StrictUnit.Rec)
module SUA = Catt.Typecheck.Make(StrictUnitAssoc.Rec)

let () = 
    Js.export_all
    (object%js
      method parse s =
          s |> Js.to_string |> parse_stringify |> Js.string
      method typecheckweak s =
          let r = try
              let defs = parse_string (Js.to_string s) in
              let res = W.print_tc (W.check_defs W.empty_ctx defs) in
              res
          with _ -> Printf.sprintf "Failure" in
          Js.string r
      method typechecksu s =
          let r = try
              let defs = parse_string (Js.to_string s) in
              let res = SU.print_tc (SU.check_defs SU.empty_ctx defs) in
              res
          with _ -> Printf.sprintf "Failure" in
          Js.string r
      method typechecksua s =
          let r = try
              let defs = parse_string (Js.to_string s) in
              let res = SUA.print_tc (SUA.check_defs SUA.empty_ctx defs) in
              res
          with _ -> Printf.sprintf "Failure" in
          Js.string r
    end)

