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

let reconstruct_symbol (fp : string) : string * (int * Lp_tree.prov) list =
  let replay = Parse_replay.parse_file fp in
  let tree = Proof_tree.build replay.rules in
  (* No flatten_binds: the goal is rendered with its binders NESTED exactly as PP
     records them, and the §A.7–8 regroupement is emitted for real (ALL1–4 / XST1–4
     `refine NAME _`, P inferred) rather than pre-merged at the AST level.  PP runs
     those merges before any consumer (ALL7/NRM/…), so by the time a compound
     `Tuple n` binder is needed the emitted merges have produced it. *)
  let goal = goal_of_tree tree in
  Emit_lp.emit_symbol (name_of_file fp) goal tree
