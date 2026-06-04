(* Translate a rebuilt proof tree into a Lambdapi tactic script.  The
   per-rule dispatch, hypothesis/witness/INS searches, and Res-chain
   handling are all internal (see [Emit_ctx], [Rule_emit], and this
   module's body); only the entry point is exposed. *)

val translate : Proof_tree.pp_tree -> Lp_tree.t
