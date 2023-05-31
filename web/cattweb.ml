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

let print_to_js s : unit =
    let s = Js.string s in
    Js.Unsafe.fun_call (Js.Unsafe.js_expr "printJS") [| Js.Unsafe.inject s |]

let () = 
    Sys_js.set_channel_flusher Stdlib.stdout print_to_js;
    Js.export_all
    (object%js
      method parse s =
          s |> Js.to_string |> parse_stringify |> Js.string
      method typecheckweak s =
          try
              let defs = parse_string (Js.to_string s) in
              W.run_tc (W.check_defs W.empty_ctx defs)
          with _ -> Printf.printf "Failure\n%!"
      method typechecksu s =
          try
              let defs = parse_string (Js.to_string s) in
              SU.run_tc (SU.check_defs SU.empty_ctx defs)
          with _ -> Printf.printf "Failure\n%!"
      method typechecksua s =
          try
              let defs = parse_string (Js.to_string s) in
              SUA.run_tc (SUA.check_defs SUA.empty_ctx defs)
          with _ -> Printf.printf "Failure\n%!"
    end)

