(* Collect the free variables of a goal predicate, split into Prop-valued
   and τ ι-valued, for the emitted symbol's parameter header.  The recursive
   collectors and the reserved-name/empty seeds are internal. *)

module SS : Set.S with type elt = string

type free_vars = { prop_vars : SS.t; exp_vars : SS.t }

(** Free variables of [p]: bare predicate atoms in [prop_vars], everything
    else (expression variables, applied function symbols) in [exp_vars];
    bound and reserved (VRAI/TRUE/FAUX/FALSE) names excluded. *)
val free_vars_of_prd : Syntax_pp.prd -> free_vars
