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

let parse_pp_line (lx : lexbuf) : line option =
  try
    Parser.line_eof Lexer.token lx
  with
  | Parser.Error ->
      let pos = lx.lex_curr_p in
      Printf.eprintf
        "Parser error at line %d, column %d: token '%s'\n"
        pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1)
        (Lexing.lexeme lx); None

let parse_pp_replay (fp : string) : line list =
  let ch = open_in fp in
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
  | Exit -> close_in ch; List.rev !ls
  | exn ->
      Printf.eprintf "Unexpected error parsing %s: %s\n" fp (Printexc.to_string exn);
      close_in ch; List.rev !ls
