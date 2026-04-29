(* Result computation for proof nodes.

   For each rule, what predicate does a proof of [goal] *conclude with*
   after the rule's transformation? This is the "result" predicate that
   flows up equality chains in the _1 primed context: a STOP node's
   result is its goal, AND3's result is its child's result, AND4's
   result is the conjunction of its children's results, etc.

   See emit_lp.ml's ALL7/XST8 emission: it passes [compute_result child1]
   as the R in `refine ALL7 (λ vars, R) _ _`, because R is what the _1
   equality chain ends up producing. *)

open Syntax_pp
open Proof_tree

let rec compute_result (node : proof_node) : prd =
  match node with
  | Apply { rule; goal; children; _ } ->
    let base = Rule_db.strip_suffix rule in
    match base, children with
    | "STOP", [] -> goal
    | _, [child] when Rule_args.is_hoas_identity base -> compute_result child
    | ("AND2" | "AND3" | "AND5" | "OR4" | "VR3" | "VR2" | "EVR2"
      | "NOT1" | "NOT2" | "OR1" | "IMP1" | "IMP5" | "FX1"
      | "XST7" | "EVR3" | "OPR1" | "OPR2" | "AR9"), [child] ->
      compute_result child
    | ("AND1" | "OR3" | "AND4" | "IMP3" | "OR2" | "IMP2"
      | "EQV1" | "EQV2" | "EQV3" | "EQV4"), [child1; child2] ->
      Binary (And, compute_result child1, compute_result child2)
    | "IMP4", [child] ->
      let p = match goal with Binary (Imp, p, _) -> p | _ -> goal in
      Binary (Imp, p, compute_result child)
    | "ALL8", [child] ->
      let vars = match goal with Bind (_, xs, _) -> xs | _ -> [] in
      Bind (Bang, vars, compute_result child)
    | "ALL9", [child] ->
      let h = match goal with Binary (Imp, h, _) -> h | _ -> goal in
      Binary (Imp, h, compute_result child)
    | _ -> goal

(* --- TRUE/FALSE simplification, used when a two-child rule's raw
   result conjunction collapses because one side is ⊤ or ⊥. --- *)

let is_true = function Lift (Var ("VRAI" | "TRUE")) -> true | _ -> false
let is_false = function Lift (Var ("FAUX" | "FALSE")) -> true | _ -> false

let rec simplify_result p =
  let prd_true = Lift (Var "VRAI") and prd_false = Lift (Var "FAUX") in
  match p with
  | Binary (And, a, b) ->
    let a = simplify_result a and b = simplify_result b in
    if is_false a || is_false b then prd_false
    else if is_true a then b else if is_true b then a
    else Binary (And, a, b)
  | Binary (Or, a, b) ->
    let a = simplify_result a and b = simplify_result b in
    if is_false a then b else if is_false b then a
    else if is_true a || is_true b then prd_true
    else Binary (Or, a, b)
  | Binary (Imp, a, b) ->
    let a = simplify_result a and b = simplify_result b in
    if is_true a then b else if is_false a then prd_true
    else Binary (Imp, a, b)
  | Unary (Not, a) ->
    let a = simplify_result a in
    if is_true a then prd_false else if is_false a then prd_true
    else (match a with Unary (Not, x) -> x | _ -> Unary (Not, a))
  | Eq (e1, e2) when e1 = e2 -> prd_true
  | _ -> p
