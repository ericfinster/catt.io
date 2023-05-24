(*****************************************************************************)
(*                                                                           *)
(*                                Web Main                                   *)
(*                                                                           *)
(*****************************************************************************)

open Catt.Io
open Js_of_ocaml
       
let () = 
    Js.export_all
    (object%js
      method parse s =
          s |> Js.to_string |> parse_string |> Js.string
    end)

