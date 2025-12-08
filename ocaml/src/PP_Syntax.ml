
type frm
type exp
type prd =
  | And of prd * prd
  | Or of prd * prd
  | Imp of prd * prd
  | Iff of prd * prd
  | Not of prd
  | All of string list * prd
  | Exi of string list * prd
  | Eq of exp * exp
  | Formula of frm

type step = (string * int option)
