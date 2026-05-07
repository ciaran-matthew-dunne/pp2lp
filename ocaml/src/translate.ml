open Syntax_pp

module P = Proof_tree
module L = Lp_tree

type ctx = {
  mutable n : int;
  mutable hyps : string list;
}

let create_ctx () = { n = 0; hyps = [] }

let fresh_h ctx =
  ctx.n <- ctx.n + 1;
  let h = Printf.sprintf "_h%d" ctx.n in
  ctx.hyps <- h :: ctx.hyps;
  h

let fresh_x ctx =
  ctx.n <- ctx.n + 1;
  Printf.sprintf "_x%d" ctx.n

let scoped_hyps ctx f =
  let saved = ctx.hyps in
  Fun.protect ~finally:(fun () -> ctx.hyps <- saved) f

let base = Rule_db.base_of

let emit_words rule =
  match Rule_db.emit_args rule with
  | None -> []
  | Some spec ->
    String.split_on_char ' ' spec |> List.filter ((<>) "")

let is_trust_spec rule =
  match emit_words rule with
  | [] -> false
  | words -> List.for_all ((=) "trust") words

let dynamic_value_args rule arg =
  match Rule_db.emit_args rule, arg with
  | Some "dynamic:ar3", Some (PipeArg (a, _b)) -> [L.Exp a]
  | Some "dynamic:ar9", Some (Pred p) -> [L.Pred p]
  | _, _ -> []

let metadata_extra_args rule =
  match Rule_db.emit_args rule with
  | None -> []
  | Some "dynamic:ar3"
  | Some "dynamic:ar9"
  | Some "dynamic:hyp" -> []
  | Some _ when is_trust_spec rule -> []
  | Some _ -> [L.Hole]

let slot_hole_args rule =
  let trusts = ref (emit_words rule) in
  Rule_db.slots rule
  |> List.map (function
    | Rule_db.Con ->
      (match !trusts with
       | "trust" :: rest -> trusts := rest; L.Trust
       | _ -> L.Hole)
    | Rule_db.Seq | Rule_db.Res -> L.Hole)

let default_rule_args rule arg =
  dynamic_value_args rule arg @ metadata_extra_args rule @ slot_hole_args rule

let replace_last args last =
  match List.rev args with
  | [] -> [last]
  | _ :: rest -> List.rev (last :: rest)

let tactic_for_rule ctx rule arg children =
  if Rule_db.emit_args rule = Some "dynamic:hyp" && children = [] then begin
    let default_args = default_rule_args rule arg in
    match ctx.hyps with
    | [] -> L.Refine (rule, default_args)
    | hyps ->
      let attempts =
        List.map
          (fun h -> L.Refine (rule, replace_last default_args (L.Name h)))
          (List.rev hyps)
      in
      L.Orelse attempts
  end else
    L.Refine (rule, default_rule_args rule arg)

let rec tree ctx = function
  | P.Apply { rule; children = [c]; _ }
    when Rule_db.is_hoas_identity (base rule) ->
    tree ctx c
  | P.Apply { rule; children = [c0; c1]; _ }
    when base rule = "ALL7" || base rule = "XST8" ->
    branching ctx rule c0 c1
  | P.Apply { rule; arg; children } ->
    default ctx rule arg children

and default ctx rule arg children =
  match children with
  | [c] when base rule = "OPR1" || base rule = "OPR2" ->
    (* OPR1: (x = E) ⇒ P x — assume the equality and rewrite x ↦ E.
       OPR2: (E = x) ⇒ P x — same but rewrite right-to-left. *)
    let h = fresh_h ctx in
    let rtl = base rule = "OPR2" in
    L.Assume (h,
      L.Then (L.Rewrite { rtl; name = h }, tree ctx c))
  | _ ->
    let tactic = tactic_for_rule ctx rule arg children in
    match children with
    | [] -> L.Step tactic
    | [c] when Rule_db.intro_antecedent rule ->
      let h = fresh_h ctx in
      L.Assume_then (tactic, h, tree ctx c)
    | [c] when base rule = "ALL8" ->
      let x = fresh_x ctx in
      L.Assume_then (tactic, x, tree ctx c)
    | [c] ->
      let child = tree ctx c in
      L.Then (tactic, child)
    | [c0; c1] ->
      let left = scoped_hyps ctx (fun () -> tree ctx c0) in
      let right = scoped_hyps ctx (fun () -> tree ctx c1) in
      L.Branches (tactic, left, right)
    | _ ->
      failwith (Printf.sprintf
        "translate: %s arity %d unsupported"
        rule (List.length children))

and branching ctx rule chain_node cont =
  let quant_sym = if base rule = "ALL7" then "ALL7" else "XST8" in
  let tactic = L.Refine (quant_sym, [L.Hole; L.Hole]) in
  let v = fresh_x ctx in
  let chain_proof = scoped_hyps ctx (fun () ->
    L.Assume (v, chain_tree ctx chain_node))
  in
  let cont_proof = scoped_hyps ctx (fun () -> tree ctx cont) in
  L.Branches (tactic, chain_proof, cont_proof)

(* The Res-chain handed to ALL7/XST8 has type `Π v : Tuple n, Res (P v)`,
   so it must be entered as a subproof: `assume v` binds the tuple at its
   correct (Lambdapi-inferred) type, and each chain step is then a `refine`
   in sequence — just like the regular proof tree, but with the primed
   Res-typed rule forms. *)
and chain_tree ctx = function
  | P.Apply { rule; children = []; arg } ->
    let args = dynamic_value_args rule arg @ slot_hole_args rule in
    L.Step (L.Refine (rule, args))
  | P.Apply { rule; children = [c]; _ } when base rule = "ALL8" ->
    let x = fresh_x ctx in
    let tactic = L.Refine (rule, [L.Hole]) in
    L.Assume_then (tactic, x, chain_tree ctx c)
  | P.Apply { rule; arg; children = [c] } ->
    let tactic =
      L.Refine (rule, dynamic_value_args rule arg @ slot_hole_args rule)
    in
    L.Then (tactic, chain_tree ctx c)
  | P.Apply { rule; arg; children = [c0; c1] } ->
    let tactic =
      L.Refine (rule, dynamic_value_args rule arg @ slot_hole_args rule)
    in
    let left = scoped_hyps ctx (fun () -> chain_tree ctx c0) in
    let right = scoped_hyps ctx (fun () -> chain_tree ctx c1) in
    L.Branches (tactic, left, right)
  | P.Apply { rule; children; _ } ->
    failwith (Printf.sprintf
      "translate: chain %s arity %d unsupported"
      rule (List.length children))

let translate (pp_tree : P.pp_tree) : L.t =
  tree (create_ctx ()) pp_tree
