(* Parse a PP `.trace` file.

   The trace format is one entry per line:

     " [RULE] &"
     " [RULE(arg)] &"
     " [FIN(predicate)] &"
     " [STOP_NORM] &"
     " [NRM] &"
     "  (formula)"   (* final line: the original goal *)

   Trace lines are emitted by PP in right-first DFS postorder of the
   proof tree (children before parents, root rule last).  The single
   `(formula)` line at the bottom carries the original goal predicate.

   This module produces:
     trace = { rules : Syntax_pp.lhs list; goal : Syntax_pp.prd }
   where [rules] preserves the file's order. *)

open Syntax_pp

type trace = {
  rules : lhs list;
  goal  : prd;
}

exception Bad_trace of string

let bad fmt = Printf.ksprintf (fun s -> raise (Bad_trace s)) fmt

(* Strip leading UTF-8 BOM (PP writes one at the start of every trace),
   then leading and trailing whitespace. *)
let utf8_bom = "\xef\xbb\xbf"
let strip_bom s =
  if String.length s >= 3
     && String.sub s 0 3 = utf8_bom
  then String.sub s 3 (String.length s - 3)
  else s

let trim s = String.trim (strip_bom s)

(* True if [s] starts with the bracketed-rule form `[…] &`. *)
let is_rule_line s =
  let s = trim s in
  String.length s > 0 && s.[0] = '['

(* True if [s] is the parenthesised goal form `(formula)`. *)
let is_goal_line s =
  let s = trim s in
  String.length s > 0 && s.[0] = '('

let parse_lhs (line : string) : lhs =
  let lx = Lexing.from_string line in
  match Parser.trace_lhs_eof Lexer.token lx with
  | Some l -> l
  | None -> bad "empty rule line"
  | exception Parser.Error ->
    let pos = lx.lex_curr_p in
    bad "rule-line parse error at column %d in %S (token %S)"
      (pos.pos_cnum - pos.pos_bol + 1)
      line
      (Lexing.lexeme lx)

let parse_goal (line : string) : prd =
  let lx = Lexing.from_string line in
  match Parser.trace_goal_eof Lexer.token lx with
  | Some p -> p
  | None -> bad "empty goal line"
  | exception Parser.Error ->
    let pos = lx.lex_curr_p in
    bad "goal-line parse error at column %d in %S (token %S)"
      (pos.pos_cnum - pos.pos_bol + 1)
      line
      (Lexing.lexeme lx)

let parse_file (path : string) : trace =
  let ic = open_in path in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
    let rules = ref [] in
    let goal = ref None in
    let lineno = ref 0 in
    (try while true do
      incr lineno;
      let line = input_line ic in
      let t = trim line in
      if t = "" then ()
      else if is_rule_line t then begin
        if !goal <> None then
          bad "rule line %d after the goal in %s" !lineno path;
        rules := parse_lhs t :: !rules
      end
      else if is_goal_line t then begin
        if !goal <> None then
          bad "second goal line at %d in %s" !lineno path;
        goal := Some (parse_goal t)
      end
      else
        bad "unrecognised line %d in %s: %S" !lineno path line
    done with End_of_file -> ());
    let goal = match !goal with
      | Some g -> g
      | None -> bad "no goal line in %s" path
    in
    { rules = List.rev !rules; goal })
