(* Parse a PP `.replay` file.

   The replay format is one entry per line:

     "[RULE] <formula>"
     "[RULE(arg)] <formula>"
     "[FIN(predicate)] <FIN(formula | sequent | sequent | int)>"
     "[STOP_NORM] <formula>"
     "[NRM] <formula>"

   The REPLAY output is not the `.trace` postorder with annotations.
   Its main sequent proof is root-first, but result-chain children of
   branching rules are emitted before the branch rule itself.  Tree
   reconstruction is therefore replay-native and lives in [Proof_tree].
   There is no separate goal line; the first rule's annotation is the
   overall goal.

   This module produces:
     replay = { rules : (Syntax_pp.lhs * Syntax_pp.rhs) list }
   where [rules] preserves the replay file's order. *)

open Syntax_pp

type replay = {
  (* Each rule line with its 1-indexed source line in the .replay file,
     threaded through to the proof tree for provenance comments. *)
  rules : (lhs * rhs * int) list;
}

exception Bad_replay of string

let bad fmt = Printf.ksprintf (fun s -> raise (Bad_replay s)) fmt

let utf8_bom = "\xef\xbb\xbf"
let strip_bom s =
  if String.length s >= 3
     && String.sub s 0 3 = utf8_bom
  then String.sub s 3 (String.length s - 3)
  else s

let trim s = String.trim (strip_bom s)

let is_replay_line s =
  let s = trim s in
  String.length s > 0 && s.[0] = '['

let parse_line (line : string) : lhs * rhs =
  let lx = Lexing.from_string line in
  match Parser.line_eof Lexer.token lx with
  | Some l -> l
  | None -> bad "empty replay line"
  | exception Parser.Error ->
    let pos = lx.lex_curr_p in
    bad "replay-line parse error at column %d in %S (token %S)"
      (pos.pos_cnum - pos.pos_bol + 1)
      line
      (Lexing.lexeme lx)

let parse_file (path : string) : replay =
  let ic = open_in path in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
    let lines = ref [] in
    let lineno = ref 0 in
    (try while true do
      incr lineno;
      let line = input_line ic in
      let t = trim line in
      if t = "" then ()
      else if is_replay_line t then
        (let (l, r) = parse_line t in
         lines := (l, r, !lineno) :: !lines)
      else
        bad "unrecognised line %d in %s: %S" !lineno path line
    done with End_of_file -> ());
    let rules = List.rev !lines in
    if rules = [] then bad "no rule lines in %s" path;
    { rules })
