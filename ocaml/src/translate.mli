(* Translate a rebuilt proof tree into a Lambdapi tactic script.  The
   per-rule dispatch, hypothesis/witness/INS searches, and Res-chain
   handling are all internal (see [Emit_ctx], [Rule_emit], and this
   module's body); only the entry point is exposed. *)

(* Returns the tactic script and the boolean-typing premises (name, LP type)
   the BOOL31/32/41/42 rules discharge — `Π u, prj k u ϵ BOOL` typings (a
   B-typing fact lost in extraction) that become extra hypotheses on the
   emitted symbol's header. *)
val translate : Proof_tree.pp_tree -> Lp_tree.t * (string * string) list
