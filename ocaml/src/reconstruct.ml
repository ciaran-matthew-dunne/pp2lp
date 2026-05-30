(* Top-level: read a `.replay` file → emit a Lambdapi proof string. *)

let is_simple_ident = Pp_lp.is_simple_ident

let name_of_file (fp : string) : string =
  let stem = Filename.remove_extension (Filename.basename fp) in
  if is_simple_ident stem then stem
  else Printf.sprintf "{|%s|}" stem

let goal_of_tree tree =
  match Proof_tree.anno_of tree with
  | Some anno -> Syntax_pp.prd_of_rhs anno
  | None -> failwith "root node of proof tree has no annotation"

let reconstruct_symbol (fp : string) : string =
  let replay = Parse_replay.parse_file fp in
  let tree = Proof_tree.build replay.rules in
  let goal = Syntax_pp.flatten_binds (goal_of_tree tree) in
  Emit_lp.emit_symbol (name_of_file fp) goal tree
