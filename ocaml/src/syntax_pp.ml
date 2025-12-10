
type uop =
  | Not
and bop =
  | Eq | Or | And | Imp | Iff
and binder =
  | Forall0 | Forall1 | Forall2 | Exists

type prd =
  | Lift of exp
  | Unary of uop * prd
  | Binary of bop * prd * prd
  | Bind of binder * string list * prd
  | Mem of exp list * exp
  | Eq of exp * exp
and exp =
  | Var of string
  | App of string * exp list

type arg =
  | Index of int
  | Pred of prd
  | Exp of string
and sequent =
  prd list * prd
and lhs =
  string * arg option
and rhs =
  | Simple of prd
  | Fin of prd * sequent * sequent * int
and line =
  lhs * rhs
