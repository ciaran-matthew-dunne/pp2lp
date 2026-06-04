(* Render the PP AST back to PP surface syntax.  Used for the goal strings
   in provenance and the `rules`/`tree` debug dumps — distinct from [Pp_lp],
   which renders the AST to *Lambdapi*.  The precedence machinery and the
   buffer-based workers are internal. *)

(** A PP predicate as PP source. *)
val prd_to_pp : Syntax_pp.prd -> string
