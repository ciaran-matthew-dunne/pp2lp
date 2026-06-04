(* Parse a PP `.replay` file into its ordered rule lines.  The BOM/whitespace
   handling and the per-line lexer/parser plumbing are internal; only the
   file entry point and the result type are exposed.  Tree reconstruction
   from these lines lives in [Proof_tree]. *)

type replay = {
  (* Each rule line with its 1-indexed source line in the .replay file,
     threaded through to the proof tree for provenance. *)
  rules : (Syntax_pp.lhs * Syntax_pp.rhs * int) list;
}

exception Bad_replay of string

(** Parse [path]; raises [Bad_replay] on a malformed or empty file. *)
val parse_file : string -> replay
