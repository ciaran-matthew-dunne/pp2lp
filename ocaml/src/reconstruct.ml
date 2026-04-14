open Proof_tree

(* Extract goal predicate from the root of a proof tree *)
let goal_of_tree = function
  | Apply { goal; _ } -> goal

let is_simple_ident = Pp_lp.is_simple_ident

(* Derive a symbol name from a filename, quoting only if needed *)
let name_of_file (fp : string) : string =
  let base = Filename.basename fp in
  let stem =
    if Filename.check_suffix base ".replay" then
      Filename.chop_suffix base ".replay"
    else if Filename.check_suffix base ".trace.replay" then
      Filename.chop_suffix base ".trace.replay"
    else base
  in
  if is_simple_ident stem then stem
  else Printf.sprintf "{|%s|}" stem

(* Reconstruct a replay file into a full Lambdapi file (header + symbol) *)
let reconstruct_file (fp : string) : string =
  let lines = Parse_pp.parse_pp_replay fp in
  if lines = [] then
    failwith (Printf.sprintf "reconstruct: no lines parsed from %s" fp);
  let tree = Proof_tree.build lines in
  let goal = goal_of_tree tree in
  let name = name_of_file fp in
  Emit_lp.emit_lp name goal tree

(* Reconstruct a replay file into just the symbol (no header) *)
let reconstruct_symbol (fp : string) : string =
  let lines = Parse_pp.parse_pp_replay fp in
  if lines = [] then
    failwith (Printf.sprintf "reconstruct: no lines parsed from %s" fp);
  let tree = Proof_tree.build lines in
  let goal = goal_of_tree tree in
  let name = name_of_file fp in
  Emit_lp.emit_symbol name goal tree

(* Reconstruct from a line list directly *)
let reconstruct_lines (name : string) (lines : Syntax_pp.line list) : string =
  if lines = [] then
    failwith "reconstruct: empty line list";
  let tree = Proof_tree.build lines in
  let goal = goal_of_tree tree in
  Emit_lp.emit_lp name goal tree
