(* Top-level: read a `.trace` file → emit a Lambdapi proof string. *)

let is_simple_ident = Pp_lp.is_simple_ident

let name_of_file (fp : string) : string =
  let stem = Filename.remove_extension (Filename.basename fp) in
  if is_simple_ident stem then stem
  else Printf.sprintf "{|%s|}" stem

let reconstruct_file (fp : string) : string =
  let trace = Parse_trace.parse_file fp in
  let tree = Proof_tree.build trace.rules in
  Emit_lp.emit_lp (name_of_file fp) trace.goal tree

let reconstruct_symbol (fp : string) : string =
  let trace = Parse_trace.parse_file fp in
  let tree = Proof_tree.build trace.rules in
  Emit_lp.emit_symbol (name_of_file fp) trace.goal tree
