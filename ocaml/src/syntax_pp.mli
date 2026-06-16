(* PP-side abstract syntax: the AST the replay parser produces and every
   later stage consumes.  The types are fully public (matched and built
   throughout the pipeline); only the substitution/normalisation helpers
   are exposed as functions — [subst_exp] is an internal detail of
   [subst_prd]. *)

type uop =
  | Not
  | Instanciation  (* PP's __INSTANCIATION(P) marker — logically P; kept as a
                      tag for the (future) FIN_INS evidence dispatch *)
and bop =
  | Or | And | Imp | Iff
and aop =
  | Add | Sub
and binder =
  | Bang     (* !x. — PP's default universal quantifier *)
  | Forall   (* forall x. — keyword form *)
  | Forall2  (* forall2 x. — second-order *)
  | Exists   (* #x. — existential quantifier *)

type prd =
  | Lift of exp
  | Unary of uop * prd
  | Binary of bop * prd * prd
  | Bind of binder * string list * prd
  | Mem of exp list * exp
  | Eq of exp * exp
  | Leq of exp * exp
  | Rel of string * exp list    (* uninterpreted Prop-valued operator applied
                                   directly: S <: T ↦ Rel ("subset", [S; T]) *)
and exp =
  | Var of string
  | Nat of int
  | BigNat of string            (* decimal literal too big for native int
                                   (e.g. 2⁶⁴ uint64 bounds in apero); an opaque
                                   atom, rendered via B.lp's int_lit coercion *)
  | App of string * exp list    (* B-function application f(x): a set of pairs
                                   applied via `eapp` to its argument(s) *)
  | EApp of exp * exp list      (* application of a non-symbol head: r~(s),
                                   {}(s), (r;s)(x) — emits `eapp <head> args` *)
  | SetOp of string * exp list  (* uninterpreted higher-order operator applied
                                   directly (NOT via eapp): S --> T, r <+ s,
                                   r ; s, S * T ↦ SetOp (name, [a; b]) *)
  | AOp of aop * exp * exp
  | Neg of exp
  | SetImage of exp * exp
  | Inter of exp * exp
  | Union of exp * exp
  | Range of exp * exp
  | Maplet of exp * exp
  | Inverse of exp
  | SetLit of exp list
  | DomRestrict of exp * exp
  | RanRestrict of exp * exp
  | BoolOf of prd               (* bool(P): cast a predicate to a BOOL element *)
  | Compr of string * string list * prd * exp
                                (* set-builder / aggregate binder:
                                   %(xs).(P | E) ↦ ("set_lambda", xs, P, E),
                                   SIGMA(xs).(P | E) ↦ ("sigma", …).  Binds xs
                                   over both P and E; string is the LP kernel. *)

type arg =
  | Pred of prd
  | PipeArg of exp * exp
and sequent =
  prd list * prd
and lhs =
  string * arg option
and rhs =
  | Simple of prd
  | Fin of prd * sequent * sequent * int
and line =
  lhs * rhs

(** B built-in set/relation operators (card, dom, ran, …) — "too big" to be
    object-level B-functions, so applied directly (not via [eapp]) with their own
    arrow types.  The emitter and [Free_vars] both key on this list. *)
val meta_ops : string list

(** Collapse consecutive same-binder [Bind]s into one compound [Bind]
    (`!x. !y. P` ↦ `!(x,y). P`), mirroring PP's ALL2/ALL3 normalisation so
    the LP side sees a single Tuple-n binder. *)
val flatten_binds : prd -> prd

(** The single shallow [exp] traversal: [map_exp f] rebuilds with [f] applied to
    each immediate sub-expression, [fold_exp f] left-folds [f] over them.  Every
    structural [exp] walker (substitution, canonicalisation, free-variable
    collection, matching) is built on these, so the per-constructor enumeration
    lives in one place. *)
val map_exp : (exp -> exp) -> exp -> exp
val fold_exp : ('a -> exp -> 'a) -> 'a -> exp -> 'a

(** First-order matching congruence: [Some] of the paired sub-expressions when
    the two expressions share constructor, payload, and arity; [None] otherwise.
    Exhaustive — a new [exp] constructor forces it to be handled. *)
val exp_congruence : exp -> exp -> (exp * exp) list option

(** Capture-permissive substitution over the PP AST, used to instantiate
    hypothesis-search patterns at chosen witness variables (AXM9, NRM19) and
    to substitute the solver witness for the pinned binder (NRM29). *)
val subst_exp : (string * exp) list -> exp -> exp
val subst_prd : (string * exp) list -> prd -> prd

(** The predicate carried by a rule annotation ([Simple] / [Fin]). *)
val prd_of_rhs : rhs -> prd
