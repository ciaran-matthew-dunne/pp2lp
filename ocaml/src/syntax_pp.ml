
type uop =
  | Not
and bop =
  | Eq | Or | And | Imp | Iff
and binder =
  | Forall0 | Forall1 | Forall2 | Exists
type term =
  | Atom of string * term list
  | Unary of uop * term
  | Binary of bop * term * term
  | Bind of binder * string list * term
  | Mem of term list * term

type arg =
  | Index of int
  | Term of term
and step =
  string * arg option
