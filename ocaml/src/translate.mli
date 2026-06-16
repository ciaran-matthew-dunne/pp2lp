(* Translate a rebuilt proof tree into a Lambdapi tactic script.  The
   per-rule dispatch, hypothesis/witness/INS searches, and Res-chain
   handling are all internal (see [Emit_ctx], [Rule_emit], and this
   module's body); only the entry point is exposed. *)

(* Returns the tactic script and the boolean- then integer-typing premises
   (name, LP type) the rules discharge — `Π u, prj k u ϵ BOOL`/`ϵ INT` typings
   (and `π (x ϵ INT)` for free vars), B-typing facts lost in extraction, that
   become extra hypotheses on the emitted symbol's header. *)
val translate :
  ?int_free_vars:Free_vars.SS.t ->
  Proof_tree.pp_tree ->
  Lp_tree.t * (string * string) list * (string * string) list
