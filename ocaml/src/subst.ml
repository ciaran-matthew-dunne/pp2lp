open Syntax_pp

let rec subst_exp x y = function
  | Var s when s = x -> Var y
  | Var _ | Nat _ | Prj _ as e -> e
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

(* ---- Substitute Var x → Prj (k, v) for tuple-binder rendering ---- *)

let rec subst_exp_to_prj x k v = function
  | Var s when s = x -> Prj (k, v)
  | Var _ | Nat _ | Prj _ as e -> e
  | App (f, args) -> App (f, List.map (subst_exp_to_prj x k v) args)
  | AOp (op, e1, e2) -> AOp (op, subst_exp_to_prj x k v e1, subst_exp_to_prj x k v e2)
  | Neg e -> Neg (subst_exp_to_prj x k v e)
  | SetImage (e1, e2) -> SetImage (subst_exp_to_prj x k v e1, subst_exp_to_prj x k v e2)
  | Inter (e1, e2) -> Inter (subst_exp_to_prj x k v e1, subst_exp_to_prj x k v e2)
  | Union (e1, e2) -> Union (subst_exp_to_prj x k v e1, subst_exp_to_prj x k v e2)

let rec subst_prd_to_prj x k v = function
  | Lift e -> Lift (subst_exp_to_prj x k v e)
  | Unary (op, p) -> Unary (op, subst_prd_to_prj x k v p)
  | Binary (op, p1, p2) ->
    Binary (op, subst_prd_to_prj x k v p1, subst_prd_to_prj x k v p2)
  | Bind (b, xs, body) ->
    (* Inner binders may shadow `x`; if so, leave the body alone. *)
    if List.mem x xs then Bind (b, xs, body)
    else Bind (b, xs, subst_prd_to_prj x k v body)
  | Mem (es, e) ->
    Mem (List.map (subst_exp_to_prj x k v) es, subst_exp_to_prj x k v e)
  | Eq (e1, e2) -> Eq (subst_exp_to_prj x k v e1, subst_exp_to_prj x k v e2)
  | Leq (e1, e2) -> Leq (subst_exp_to_prj x k v e1, subst_exp_to_prj x k v e2)

(* Substitute each `xs[k]` with `Prj (k, v)` in the body. *)
let subst_prd_to_prjs xs v body =
  let body, _ = List.fold_left (fun (b, k) x ->
    (subst_prd_to_prj x k v b, k + 1))
    (body, 0) xs
  in body
