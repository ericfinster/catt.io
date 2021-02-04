(*****************************************************************************)
(*                                                                           *)
(*                                     IO                                    *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Command
open Typecheck
open Rawcheck

open Mtl
       
open MonadSyntax(RawMnd)

(*****************************************************************************)
(*                                  Options                                  *)
(*****************************************************************************)
    
let usage = "catt [options] [file]"

let global_config = ref default_config

let enable_strict_units _ =
  printf "Using strictly unital normalization@,";
  global_config := { !global_config with norm_type = StrictlyUnital }

let spec_list = [
  ("-su", Arg.Unit enable_strict_units, "Enable strictly unital normalization")
]

(*****************************************************************************)
(*                                  Parsing                                  *)
(*****************************************************************************)

module I = Parser.MenhirInterpreter

exception Parse_error of ((int * int) option * string)
                          
let get_parse_error env =
    match I.stack env with
    | lazy Nil -> "Invalid syntax"
    | lazy (Cons (I.Element (state, _, _, _), _)) ->
        try (Parser_messages.message (I.number state)) with
        | Not_found -> "invalid syntax (no specific message for this error)"

let rec parse lexbuf (checkpoint : (string list * cmd list) I.checkpoint) =
  match checkpoint with
  | I.InputNeeded _env ->
      let token = Lexer.token lexbuf in
      let startp = lexbuf.lex_start_p
      and endp = lexbuf.lex_curr_p in
      let checkpoint = I.offer checkpoint (token, startp, endp) in
      parse lexbuf checkpoint
  | I.Shifting _
  | I.AboutToReduce _ ->
      let checkpoint = I.resume checkpoint in
      parse lexbuf checkpoint
  | I.HandlingError _env ->
      let line, pos = Lexer.get_lexing_position lexbuf in
      let err = get_parse_error _env in
      raise (Parse_error (Some (line, pos), err))
  | I.Accepted v -> v
  | I.Rejected ->
       raise (Parse_error (None, "invalid syntax (parser rejected the input)"))

let parse_file f =
  let lexbuf =
    let fi = open_in f in
    let flen = in_channel_length fi in
    let buf = Bytes.create flen in
    really_input fi buf 0 flen;
    close_in fi;
    Lexing.from_string (Bytes.to_string buf)
  in try parse lexbuf (Parser.Incremental.prog lexbuf.lex_curr_p) with 
  | Parse_error (Some (line,pos), err) ->
    printf "Parse error: %sLine: %d, Pos: %d@," err line pos;
    exit (-1)
  | Parse_error (None, err) -> 
    printf "Parse error: %s" err;
    exit (-1)
  | Lexer.Lexing_error (Some (line,pos), err) ->
    printf "Lexing error: %s@,Line: %d, Pos: %d@," err line pos;
    exit (-1)
  | Lexer.Lexing_error (None, err) -> 
    printf "Lexing error: %s@," err;
    exit (-1)

(* There has got to be a better way to pass the environment around ... *)
(* Actually, maybe the module list belongs with the raw checker!! *)
let rec raw_check_all files =
  match files with
  | [] -> raw_complete_env
  | f::fs -> 
    print_string "-----------------";
    print_cut ();
    printf "Processing input file: %s\n" f;
    let (impts, cmds) = parse_file f in
    let imprt_nms = List.map (fun fn -> fn ^ ".catt") impts in
    let* (renv, tenv) = raw_check_all imprt_nms in
    if (List.mem f tenv.modules) then
      let _ = printf "Skipping repeated import: %s@," f in
      raw_with_env renv tenv (raw_check_all fs)
    else let* (renv', tenv') = raw_with_env renv tenv (check_cmds cmds) in
      let tenv'' = { tenv' with modules = f::tenv'.modules } in 
      raw_with_env renv' tenv'' (raw_check_all fs)

let check_files files =
  let tenv = { empty_env with config = !global_config } in
  match raw_check_all files empty_raw_env tenv with
  | Ok (Ok env) -> env
    (* A total hack.  Find a graceful way ... *)
  | _ -> raise Not_found
           



