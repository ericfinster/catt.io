(*****************************************************************************)
(*                                                                           *)
(*                                     IO                                    *)
(*                                                                           *)
(*****************************************************************************)

open Format

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
        | Not_found -> "Invalid syntax (no specific message for this error)"

let rec parse lexbuf (checkpoint : 'a I.checkpoint) =
  match checkpoint with
  | I.InputNeeded _env ->
    let token = Lexer.token lexbuf in
    let (startp,endp) = Sedlexing.lexing_positions lexbuf in
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
    raise (Parse_error (None, "Invalid syntax (parser rejected the input)"))

let parse_file f =
  let fi = open_in f in
  let lexbuf = Sedlexing.Utf8.from_channel fi in
  try
    let chkpt = Parser.Incremental.prog (fst (Sedlexing.lexing_positions lexbuf)) in
    let defs = parse lexbuf chkpt in
    close_in fi;
    defs
  with
  | Parse_error (Some (line,pos), err) ->
    printf "Parse error: %sLine: %d, Pos: %d@," err line pos;
    close_in fi;
    exit (-1)
  | Parse_error (None, err) ->
    printf "Parse error: %s" err;
    close_in fi;
    exit (-1)
  | Lexer.Lexing_error (Some (line,pos), err) ->
    close_in fi;
    printf "Lexing error: %s@,Line: %d, Pos: %d@," err line pos;
    exit (-1)
  | Lexer.Lexing_error (None, err) ->
    close_in fi;
    printf "Lexing error: %s@," err;
    exit (-1)

let rec parse_all files =
  match files with
  | [] -> []
  | f::fs ->
    let dds = parse_all fs in
    print_string "-----------------";
    print_cut ();
    printf "Processing input file: %s\n" f;
    let ds = parse_file f in
    List.append ds dds
