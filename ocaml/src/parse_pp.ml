open Lexing
open Syntax_pp

let parse_pp_line (lx : lexbuf) : line option =
  try
    Parser.line_eof Lexer.token lx
  with
  | Parser.Error ->
      let pos = lx.lex_curr_p in
      Printf.printf
        "Parser error in at line %d, column %d: token '%s'\n"
        pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1)
        (Lexing.lexeme lx); None

let parse_pp_replay (fp : string) : line list =
  let ch = open_in fp in
  Printf.printf "Parsing: %s\nCharacters: %d\n"
    fp (in_channel_length ch);

  let lx = Lexing.from_channel ch in
  let ls = ref [] in
  try
    while true do
      match parse_pp_line lx with
      | Some l -> ls := l :: !ls;
      | None -> raise Exit
    done;
    assert false (* unreachable *)
  with
  | Exit -> close_in ch; !ls
  | exn -> close_in ch; []
