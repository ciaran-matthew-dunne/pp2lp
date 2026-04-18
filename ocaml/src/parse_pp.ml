open Lexing
open Syntax_pp

let parse_pp_string (s : string) : line option =
  let lx = Lexing.from_string s in
  try
    Parser.line_eof Lexer.token lx
  with
  | Parser.Error ->
      let pos = lx.lex_curr_p in
      Printf.eprintf
        "Parser error at column %d: token '%s'\n"
        (pos.pos_cnum - pos.pos_bol + 1)
        (Lexing.lexeme lx); None

(* Returns Some line on success, None on EOF.
   Raises Proof_tree.Ill_formed_replay on parser error. *)
let parse_pp_line (lx : lexbuf) : line option =
  try
    Parser.line_eof Lexer.token lx
  with
  | Parser.Error ->
      let pos = lx.lex_curr_p in
      raise (Proof_tree.Ill_formed_replay
        (Printf.sprintf "parse error at line %d, column %d: token '%s'"
          pos.pos_lnum
          (pos.pos_cnum - pos.pos_bol + 1)
          (Lexing.lexeme lx)))

let parse_pp_replay (fp : string) : line list =
  let ch = open_in fp in
  Fun.protect ~finally:(fun () -> close_in ch) (fun () ->
    let lx = Lexing.from_channel ch in
    let ls = ref [] in
    let rec loop () =
      match parse_pp_line lx with
      | Some l -> ls := l :: !ls; loop ()
      | None -> ()
    in
    loop ();
    List.rev !ls)
