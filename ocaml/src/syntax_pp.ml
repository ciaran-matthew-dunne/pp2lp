
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
