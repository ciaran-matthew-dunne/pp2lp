open Syntax_pp

let rec subst_exp x y = function
  | Var s when s = x -> Var y
  | Var _ | Nat _ as e -> e
  | App (f, args) -> App (f, List.map (subst_exp x y) args)
  | AOp (op, e1, e2) -> AOp (op, subst_exp x y e1, subst_exp x y e2)
  | Neg e -> Neg (subst_exp x y e)
  | SetImage (e1, e2) -> SetImage (subst_exp x y e1, subst_exp x y e2)
  | Inter (e1, e2) -> Inter (subst_exp x y e1, subst_exp x y e2)
  | Union (e1, e2) -> Union (subst_exp x y e1, subst_exp x y e2)

let rec subst_prd x y = function
  | Lift e -> Lift (subst_exp x y e)
  | Unary (op, p) -> Unary (op, subst_prd x y p)
  | Binary (op, p1, p2) -> Binary (op, subst_prd x y p1, subst_prd x y p2)
  | Bind (b, xs, body) ->
    if List.mem x xs then Bind (b, xs, body)
    else Bind (b, xs, subst_prd x y body)
  | Mem (es, e) -> Mem (List.map (subst_exp x y) es, subst_exp x y e)
  | Eq (e1, e2) -> Eq (subst_exp x y e1, subst_exp x y e2)
  | Leq (e1, e2) -> Leq (subst_exp x y e1, subst_exp x y e2)
