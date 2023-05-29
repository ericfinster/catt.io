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
      method typecheck_weak s =
          let r = try
              let defs = parse_string (Js.to_string s) in
              let res = W.print_tc (W.check_defs W.empty_ctx defs) in
              res
          with _ -> Printf.sprintf "Failure" in
          Js.string r
    end)

