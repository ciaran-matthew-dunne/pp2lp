(* Read one `.replay` file → emit the Lambdapi proof symbol.  Returns the
   source text and the (emitted line → provenance) map for the CLI's
   error→rule lookup. *)

val reconstruct_symbol : string -> string * (int * Lp_tree.prov) list
