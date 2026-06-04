(* Wrap a translated proof in an `opaque symbol …` declaration: the symbol
   header (free Prop / τ ι parameters), the goal type, and the tactic body.
   Returns the source text and a sink of (emitted line, provenance) pairs. *)

val emit_symbol :
  string -> Syntax_pp.prd -> Proof_tree.pp_tree ->
  string * (int * Lp_tree.prov) list
