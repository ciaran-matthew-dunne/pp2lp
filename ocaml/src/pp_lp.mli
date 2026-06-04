(* PP-side AST → Lambdapi source pretty-printing.  The precedence
   machinery, the ⋀-list/quantifier emitters, and the block-layout
   helpers are internal; only the entry points the emitter calls are
   exposed.

   [env] maps a PP variable to (projection index, tuple-var name) so that
   a var bound by an enclosing n-ary quantifier renders as `prj k v`. *)

(** Is [s] a plain Lambdapi identifier (no `{|…|}` escaping needed)? *)
val is_simple_ident : string -> bool

(** Emit an identifier, escaping to `{|…|}` when not simple. *)
val pp_ident : Buffer.t -> string -> unit

val pp_exp :
  ?min_bp:int -> ?env:(string * (int * string)) list ->
  Buffer.t -> Syntax_pp.exp -> unit

val pp_prd :
  ?min_bp:int -> ?env:(string * (int * string)) list ->
  Buffer.t -> Syntax_pp.prd -> unit

(** Block-layout predicate printer: inline if it fits [block_width],
    else broken across lines at indent [ind]. *)
val pp_prd_block :
  ?min_bp:int -> ?env:(string * (int * string)) list ->
  int -> Buffer.t -> Syntax_pp.prd -> unit

(** Flatten a ∧ tree fully into its leaves. *)
val conj_leaves : Syntax_pp.prd -> Syntax_pp.prd list

(** Split only the left spine of a left-associative ∧ tree, keeping
    right-hand sub-conjunctions as single elements. *)
val conj_children_left : Syntax_pp.prd -> Syntax_pp.prd list
