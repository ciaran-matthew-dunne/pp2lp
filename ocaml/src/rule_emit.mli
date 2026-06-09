(* Per-rule tactic construction — the middle layer.  Given a rule and its
   annotation, builds the `refine …` tactic for one proof node.  The
   refine-argument assembly, the conjunct/AND5 matching, and the per-strategy
   tactic builders are private; only the entry points [Translate] calls are
   exposed. *)

open Syntax_pp

(* A PP predicate/expression as an [Lp_tree] term, carrying the
   tuple-projection env derived from [ctx] so enclosing-binder vars render
   as `prj k x` when the printer runs. *)
val pred_term : Emit_ctx.ctx -> prd -> Lp_tree.term
val exp_term : Emit_ctx.ctx -> exp -> Lp_tree.term

(* Value/hole arguments the generic (non-tree-expanding) rules take: the
   rule's PP-side value arg ([dynamic_value_args]) and the holes/`trust` for
   its derivation slots ([slot_hole_args]). *)
val dynamic_value_args : Emit_ctx.ctx -> string -> arg option -> Lp_tree.term list
val slot_hole_args : string -> Lp_tree.term list

(* Solver side-condition args the LP signature needs before its slot holes
   (e.g. AR9's `trust` for `E = F`).  The main-tree path bundles this into
   the rule's args; the Res-chain path must include it too. *)
val metadata_extra_args : string -> Lp_tree.term list

(* AND5: locate the implication conjunct [j] whose antecedent is matched by
   the conjunct(s) at the returned positions. *)
val find_and5_pair : prd list -> (int list * int) option

(* The single `refine` tactic for a proof node.  Exhaustive over
   [Rule_db.emit]; the walker handles the tree-expanding strategies
   (And5/Opr/Ins/branching) before calling in here. *)
val tactic_for_rule :
  Emit_ctx.ctx -> string -> arg option -> rhs option ->
  Proof_tree.pp_tree list -> Lp_tree.tactic

(* Provenance for a node's primary tactic: rule, replay line, and the goal
   PP saw rendered as PP surface syntax. *)
val prov_of : string -> int -> rhs option -> Lp_tree.prov
