(* PP-side abstract syntax: the AST the replay parser produces and every
   later stage consumes.  The types are fully public (matched and built
   throughout the pipeline); only the substitution/normalisation helpers
   are exposed as functions — [subst_exp] is an internal detail of
   [subst_prd]. *)

type uop =
  | Not
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
and exp =
  | Var of string
  | Nat of int
  | App of string * exp list
  | AOp of aop * exp * exp
  | Neg of exp
  | SetImage of exp * exp
  | Inter of exp * exp
  | Union of exp * exp

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

(** Collapse consecutive same-binder [Bind]s into one compound [Bind]
    (`!x. !y. P` ↦ `!(x,y). P`), mirroring PP's ALL2/ALL3 normalisation so
    the LP side sees a single Tuple-n binder. *)
val flatten_binds : prd -> prd

(** Capture-permissive substitution over the PP AST, used to instantiate
    hypothesis-search patterns at chosen witness variables (AXM9, NRM19). *)
val subst_prd : (string * exp) list -> prd -> prd

(** The predicate carried by a rule annotation ([Simple] / [Fin]). *)
val prd_of_rhs : rhs -> prd
