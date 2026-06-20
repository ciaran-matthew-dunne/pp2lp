(* Translate a rebuilt proof tree into a Lambdapi tactic script.  The
   per-rule dispatch, hypothesis/witness/INS searches, and Res-chain
   handling are all internal (see [Emit_ctx], [Rule_emit], and this
   module's body); only the entry point is exposed. *)

(* Returns the tactic script.  A rule's `ϵ INT` / `ϵ BOOL` side-condition (a
   B-typing fact lost in extraction) is discharged in place by the typing oracle
   (B.lp `trust_int` / `trust_bool`), so nothing need be threaded to the header. *)
val translate : Proof_tree.pp_tree -> Lp_tree.t
