(* Emission context and the lookups over it.

   This is the bottom layer of the emitter: the mutable proof-construction
   state ([ctx]), the small goal/annotation helpers shared by every layer,
   and the hypothesis / witness / INS searches that read the context.  The
   per-rule tactic construction lives above it in [Rule_emit]; the proof-tree
   walker on top of that in [Translate]. *)

open Syntax_pp

module L = Lp_tree

(* The ctx-free arithmetic proof synthesis (signed-atom normalisation, the
   sum/positivity provers, the Farkas search) lives in [Arith_proofs]; open it
   so those helpers resolve unqualified here, as they did when they were
   defined in this module. *)
open Arith_proofs

(* Translation context.

   `hyps` carries the predicate each `_hN` was introduced with; the
   [Hyp_search] rules (AXM1-6, EAXM1, EAXM2) look up the predicate they
   need by structural equality.

   `xs` carries the PP-side variable names each `_xN` corresponds to (the
   binder's vars at the point we entered it). Witness-search rules (AXM9,
   NRM19) substitute those names into the rule's expected hypothesis
   pattern and look it up in `hyps`. *)
type ctx = {
  mutable n : int;
  mutable hyps : (string * prd) list;
  mutable xs : (string * string list) list;
  (* Boolean-typing premises accumulated during emission: (name, type), one
     per (arity, slot) a BOOL31/32/41/42 split needs.  [Emit_lp] adds them to
     the symbol header. *)
  mutable bool_typings : (string * string) list;
  (* Integer-typing premises, same idea: a guarded arithmetic lemma (int_retract
     in the to_int-transport / leq_antisym / AR5–8) needs `<atom> ϵ INT` evidence
     the goal extraction dropped.  Per-(arity,slot) for a bound tuple slot,
     per-name for a free var; [Emit_lp] adds them to the header. *)
  mutable int_typings : (string * string) list;
  (* The goal's free τ ι variables (the emitted symbol's `(x : τ ι)` params).
     Only these can carry an injected `π (x ϵ INT)` premise; a witness / locally
     bound var is not in scope at the header, so the emitter refuses it. *)
  int_free_vars : Free_vars.SS.t;
}

let create_ctx ?(int_free_vars = Free_vars.SS.empty) () =
  { n = 0; hyps = []; xs = [];
    bool_typings = []; int_typings = []; int_free_vars }

let fresh_h ctx pred =
  ctx.n <- ctx.n + 1;
  let h = Printf.sprintf "_h%d" ctx.n in
  ctx.hyps <- (h, pred) :: ctx.hyps;
  h

let fresh_x ctx pp_vars =
  ctx.n <- ctx.n + 1;
  let x = Printf.sprintf "_x%d" ctx.n in
  ctx.xs <- (x, pp_vars) :: ctx.xs;
  x

(* Allocate a fresh `_xN` name without registering in ctx.xs. Used for
   chain-internal binders: the chain's `assume v` keeps v scoped to the
   chain block, and the sibling cont mustn't see it as an in-scope tuple
   var. *)
let fresh_x_local ctx =
  ctx.n <- ctx.n + 1;
  Printf.sprintf "_x%d" ctx.n

let with_x ctx x pp_vars f =
  let saved = ctx.xs in
  ctx.xs <- (x, pp_vars) :: ctx.xs;
  Fun.protect ~finally:(fun () -> ctx.xs <- saved) f

let scoped_hyps ctx f =
  let saved_h = ctx.hyps in
  let saved_x = ctx.xs in
  Fun.protect ~finally:(fun () ->
    ctx.hyps <- saved_h;
    ctx.xs <- saved_x) f

let base = Rule_db.base_of

(* PP primes most rules inside a first-normalisation chain (ALL7_1, ALL9_1,
   STOP_1, IMP4_1…) but leaves NRM rules *unprimed* (it emits `[NRM14]`, not
   `[NRM14_1]`).  In a Res chain those must be the Res-typed `_1` form, so prime
   an unprimed NRM rule name when emitting it.  Metadata lookups keep using the
   base name (`base_of "NRM14_1" = "NRM14"`).  Only the NRM rules flagged
   [chain_form] in [Rule_db] actually have a `_1` Res lemma; priming a rule that
   does not is how an undefined `NRMk_1` reached lambdapi, so refuse it here with
   a stable code instead of emitting a symbol that doesn't exist. *)
let chain_emit_name rule =
  if Rule_db.is_nrm rule && not (Rule_db.is_primed rule) then
    if Rule_db.has_chain_form rule then rule ^ "_1"
    else
      Errors.fail "E_DISPATCH"
        "%s appears in a result chain but has no Res-chain `_1` form. PP emits \
         NRM rules unprimed in chains; the emitter can only prime those with a \
         `%s_1` lemma in lp/rules/Nrm.lp (flagged ~chain_form in rule_db). Add \
         that Res lemma + flag, or this occurrence can't be emitted in a chain."
        rule rule
  else rule

(* ---- LP proof-term vocabulary + ⋀-list algebra ----

   The LP lemma/symbol names the emitter references live here — the only
   place LP-side names appear outside the [Pp_lp] formula printer — together
   with the small ⋀-list proof-term algebra built on them.  Everything
   returns a structured [Lp_tree.term]; nothing renders to a string. *)

(* `prj k t` — the k-th projection, emitted as the infix `t ⋕ k` (B.lp's
   `⋕ x n ≔ prj (to_nat n) x`), matching how goal statements render tuple slots.
   The index is a bare ℤ decimal (the file is ℤ-global); `⋕` applies `to_nat`, so
   no coercion is inserted (cf. [Pp_lp.pp_idx]). *)
let prj k t =
  L.Infix ("\xe2\x8b\x95" (* ⋕ *), t, L.Name (string_of_int k))

let conj_intro a b = L.App (L.Name "\xe2\x8b\x80_intro", [a; b]) (* ⋀_intro *)
let conj_nil_prf = L.Name "\xe2\x8b\x80_nil_prf"                 (* ⋀_nil_prf *)
let true_intro = L.Name "\xe2\x8a\xa4\xe1\xb5\xa2"             (* ⊤ᵢ *)
let eq_refl t = L.App (L.Name "eq_refl", [t])

(* Build `π (⋀ (∎ ∷ e₀ ∷ … ∷ eₙ₋₁))` from element proofs: a snoc left-fold
   ⋀_intro (… (⋀_intro ⋀_nil_prf e₀) …) eₙ₋₁ bottoming in ⋀_nil_prf.
   ⋀_intro's implicits are inferred from the expected type.  A singleton
   needs no wrapping (⋀ (∎ ∷ e) ≡ e). *)
let conj_chain = function
  | [t] -> t
  | ts -> List.fold_left conj_intro conj_nil_prf ts

(* Project conjunct [k] (front-indexed, 0 = first) of the n-element ⋀-list held
   by [var], via B.lp's back-indexed `conj_prj` (index 0 = last, so a front index
   k is n-1-k).  The ⋀_init/⋀_last walk happens at reduction time, so the emitted
   term is O(1).  `conj_rm_at` likewise proves the conjunction survives dropping
   conjunct [k]. *)
let conj_prj_at var conjs k =
  let n = List.length conjs in
  L.App (L.Name "conj_prj", [L.Hole; L.Name (string_of_int (n - 1 - k)); var])

let conj_rm_at var conjs k =
  let n = List.length conjs in
  L.App (L.Name "conj_rm", [L.Hole; L.Name (string_of_int (n - 1 - k)); var])

(* AND5: modus ponens within a conjunction.  PP drops the implication conjunct
   [j] and appends its consequent, derived by applying [j] to its antecedent
   (the conjunct(s) at [ant_positions]).  O(1) emitted size: `conj_rm_at` drops
   conjunct [j], `conj_prj_at` pulls [j] and each antecedent leaf. *)
let and5_fwd var conjs ant_positions j =
  let ant_proof = conj_chain (List.map (conj_prj_at var conjs) ant_positions) in
  let discharged = L.App (conj_prj_at var conjs j, [ant_proof]) in
  conj_intro (conj_rm_at var conjs j) discharged

(* ---- Goal extraction from rule annotations ---- *)

let goal_of_anno = function
  | Some rhs -> Some (prd_of_rhs rhs)
  | None -> None

let antecedent_of = function
  | Binary (Imp, ant, _) -> Some ant
  | _ -> None

let binder_vars_of = function
  | Bind (_, vs, _) -> Some vs
  | _ -> None

let is_true_atom = function
  | Lift (Var ("VRAI" | "TRUE")) -> true
  | _ -> false

(* Locate the bound variable [v] in the in-scope tuple binders: returns the
   tuple's LP name, [v]'s slot, and the tuple's arity.  Innermost binder wins
   (ctx.xs is a stack). *)
let find_tuple_slot ctx v =
  List.find_map (fun (tname, pvs) ->
    let rec idx i = function
      | [] -> None
      | x :: _ when x = v -> Some i
      | _ :: rest -> idx (i + 1) rest
    in
    match idx 0 pvs with
    | Some k -> Some (tname, k, List.length pvs)
    | None -> None) ctx.xs

(* The `V ϵ BOOL` discharge term for a BOOL31/32/41/42 split on bound var [v]:
   a per-(arity,slot) typing premise `Π u : Tuple n, π ((u ⋕ k) ϵ BOOL)`
   (registered in [ctx.bool_typings] so [Emit_lp] adds it to the header),
   applied to the in-scope tuple.  [None] when [v] isn't a bound tuple slot. *)
let bool_typing_term ctx v =
  match find_tuple_slot ctx v with
  | Some (tname, k, n) ->
    let name = Printf.sprintf "_bt_%d_%d" n k in
    let ty =
      Printf.sprintf
        "\xce\xa0 u : Tuple %d, \xcf\x80 ((u \xe2\x8b\x95 %d) \xcf\xb5 BOOL)" n k
    in
    if not (List.mem_assoc name ctx.bool_typings) then
      ctx.bool_typings <- ctx.bool_typings @ [ (name, ty) ];
    Some (L.App (L.Name name, [ L.Name tname ]))
  | None -> None

(* `V ϵ INT` evidence for an integer-typed variable [v]: like [bool_typing_term],
   a bound tuple slot discharges from a per-(arity,slot) `Π u, (u ⋕ k) ϵ INT`
   premise applied to the in-scope tuple; a *free* var (a `(x : τ ι)` symbol
   param) from a per-name `π (x ϵ INT)` premise.  Both injected into
   [ctx.int_typings] for [Emit_lp]'s header — morally true (the var IS an
   integer), exactly the BOOL pattern, not a postulate. *)
let int_typing_term ctx v : L.term =
  match find_tuple_slot ctx v with
  | Some (tname, k, n) ->
    let name = Printf.sprintf "_it_%d_%d" n k in
    let ty =
      Printf.sprintf
        "\xce\xa0 u : Tuple %d, \xcf\x80 ((u \xe2\x8b\x95 %d) \xcf\xb5 INT)" n k
    in
    if not (List.mem_assoc name ctx.int_typings) then
      ctx.int_typings <- ctx.int_typings @ [ (name, ty) ];
    L.App (L.Name name, [ L.Name tname ])
  | None when not (Free_vars.SS.mem v ctx.int_free_vars) ->
    (* Not a tuple slot and not a goal free var → a witness / locally bound var.
       Its `ϵ INT` evidence can't be a header premise (out of scope there), so
       refuse rather than emit a dangling reference.  A genuine frontier: proving
       an introduced witness is an integer needs evidence the replay doesn't carry. *)
    Errors.fail "E_EMIT"
      "no INT evidence for the witness/bound variable %s (not a goal free \
       variable, so no header typing premise can name it)" v
  | None ->
    (* genuine free integer var: `_iv_<sanitised v> : π (v ϵ INT)`.  ponytail: the
       sanitised name could in principle collide for two distinct vars, but
       lambdapi then rejects the duplicate param (loud), never silent. *)
    let sani = String.map (fun c ->
      if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
         || (c >= '0' && c <= '9') || c = '_' then c else '_') v in
    let name = "_iv_" ^ sani in
    let ty =
      let b = Buffer.create 32 in
      Buffer.add_string b "\xcf\x80 ("; (* π ( *)
      Pp_lp.pp_ident b v;
      Buffer.add_string b " \xcf\xb5 INT)";
      Buffer.contents b
    in
    if not (List.mem_assoc name ctx.int_typings) then
      ctx.int_typings <- ctx.int_typings @ [ (name, ty) ];
    L.Name name

(* The atom resolver [Arith_proofs.int_evidence] defers to (set in [Translate]):
   an integer-typed atom's `ϵ INT` evidence is its typing premise; a non-variable
   atom (a B-function image, set operator) in an arithmetic position has no such
   premise, so fail loud rather than invent one. *)
let atom_int_evidence ctx e : L.term =
  match e with
  | Var v -> int_typing_term ctx v
  | _ ->
    Errors.fail "E_EMIT"
      "no INT evidence for the non-variable arithmetic atom %s"
      (Emit_pp.prd_to_pp (Lift e))

(* ---- Hyp lookup: derive the needed predicate from the goal ----

   Each `Hyp_search` rule has a fixed LP-type signature; the hypothesis
   it expects is a function of the goal. This table mirrors the signatures
   in lp/rules/Axm.lp, Impl.lp, Eq.lp. *)

let expected_hyp_pred rule goal =
  match base rule, goal with
  | "AXM1", Binary (Imp, p, _) -> Some (Unary (Not, p))
  | "AXM2", Binary (Imp, Unary (Not, p), _) -> Some p
  | "AXM3", p -> Some p
  | "AXM4", Binary (Imp, _, r) -> Some r
  | "AXM5", Binary (Imp, _, Binary (Imp, q, _)) -> Some (Unary (Not, q))
  | "AXM6", Binary (Imp, _, Binary (Imp, Unary (Not, q), _)) -> Some q
  | "EAXM1", Binary (Imp, Eq (e, f), _) ->
    (* lp/rules/Eq.lp EAXM1 expects π (¬ (F = E)) — the swap is in the spec *)
    Some (Unary (Not, Eq (f, e)))
  | "EAXM2", Binary (Imp, Unary (Not, Eq (e, f)), _) ->
    Some (Eq (f, e))
  (* EAXM31/32 close the goal itself from its commuted-equality hyp. *)
  | "EAXM31", Eq (e, f) -> Some (Eq (f, e))
  | "EAXM32", Unary (Not, Eq (e, f)) -> Some (Unary (Not, Eq (f, e)))
  | _ -> None

let find_hyp_by_pred ctx pred =
  List.find_map
    (fun (name, p) -> if p = pred then Some name else None) ctx.hyps

(* ---- EQS2 / ECTR3 store-evidence searches ---- *)

let is_eql_set_app e f p =
  match p with
  | Lift (App (g, [e'; f'])) ->
    (g = "_eql_set" || g = "eql_set") && e' = e && f' = f
  | _ -> false

(* PP's EQS2 discharges `¬ _eql_set(E,F)` outright (spec p.98: its premise
   is FAUX ⇒ R) — sound because the marker, or the `E = F` it stands for,
   is still in PP's hypothesis store.  Find that store fact among the
   assumed hyps. *)
let find_eqs2_hyp ctx e f =
  List.find_map
    (fun (name, p) ->
       if p = Eq (e, f) then Some (name, true)
       else if is_eql_set_app e f p then Some (name, false)
       else None)
    ctx.hyps

(* EQS2 evidence from the inclusion pair: the refuted-inclusion universal
   `forall2(x).not(x:E and not(x:F))` for both directions (the form PP's
   normalisation leaves in the store when the equality itself was split
   into another branch). *)
let is_refuted_incl e f p =
  match p with
  | Bind (_, [v], Unary (Not, Binary (And,
      Mem ([Var v1], e'), Unary (Not, Mem ([Var v2], f'))))) ->
    v1 = v && v2 = v && e' = e && f' = f
  | _ -> false

let find_eqs2_incl_pair ctx e f =
  let find pred =
    List.find_map (fun (n, p) -> if pred p then Some n else None) ctx.hyps
  in
  match find (is_refuted_incl e f), find (is_refuted_incl f e) with
  | Some h1, Some h2 -> Some (h1, h2)
  | _ -> None

(* EQS2 fallback: the marker is still an *antecedent of R* (the original
   hypothesis conjunction has not been introduced yet) — possibly nested
   inside a right-nested conjunct (`x = y and (incls and marker)`).  Walk
   R's implication spine; within each antecedent, find a ⋀-projection
   path to the marker: one (conjunct count, index) step per nesting
   level, following the renderer's left-assoc flattening.  Returns
   (antecedents before it, the path). *)
let find_eqs2_spine e f r =
  let rec marker_path p =
    if is_eql_set_app e f p then Some []
    else
      match p with
      | Binary (And, _, _) ->
        let conjs = Pp_lp.conj_children_left p in
        let n = List.length conjs in
        let rec try_at k = function
          | [] -> None
          | c :: tl ->
            (match marker_path c with
             | Some path -> Some ((n, k) :: path)
             | None -> try_at (k + 1) tl)
        in
        try_at 0 conjs
      | _ -> None
  in
  let rec walk n r =
    match r with
    | Binary (Imp, a, rest) ->
      (match marker_path a with
       | Some path -> Some (n, path)
       | None -> walk (n + 1) rest)
    | _ -> None
  in
  walk 0 r

(* ECTR3/4 discharge `¬(P E) ⇒ Q` from store hyps `E = F` (ECTR3) or
   `F = E` (ECTR4) and `P F`.  From the negated goal atom [g] = `P E`, find an
   equality hyp one side of which (the rewritten side `E`, a variable *or* a
   compound term like `f(x)`) occurs in [g]; rewriting it to the other side `F`
   must yield another hyp `P F`.  Returns the rewritten sub-expression `E`, the
   equality hyp, whether it is recorded as F = E (→ ECTR4), and the `P F` hyp. *)
let find_ectr34 ctx g =
  let try_dir e_from e_to heq swapped =
    let g' = replace_subexp_prd e_from e_to g in
    if g' = g then None
    else
      List.find_map
        (fun (h_name, q) ->
           if q = g' then Some (e_from, heq, swapped, h_name) else None)
        ctx.hyps
  in
  List.find_map
    (fun (he, p) ->
       match p with
       | Eq (e1, e2) ->
         (match try_dir e1 e2 he false with
          | Some r -> Some r
          | None -> try_dir e2 e1 he true)
       | _ -> None)
    ctx.hyps

(* ECTR1/2: conclusion `(a = b) ⇒ P` (ECTR2: read as (F = E)).  Store
   premises ¬(Q E) and Q F.  Returns (E-var, Q's body from the ¬-hyp,
   the ¬-hyp, the F-hyp, swapped = ECTR2). *)
let find_ectr12 ctx a b =
  let try_dir e f swapped =
    match e with
    | Var x ->
      List.find_map
        (fun (hn, p) ->
           match p with
           | Unary (Not, q) ->
             let q' = subst_prd [(x, f)] q in
             if q' = q then None
             else
               List.find_map
                 (fun (hh, p') ->
                    if p' = q' then Some (x, q, hn, hh, swapped) else None)
                 ctx.hyps
           | _ -> None)
        ctx.hyps
    | _ -> None
  in
  (match try_dir a b false with
   | Some r -> Some r
   | None -> try_dir b a true)

(* ECTR5/6: conclusion `G ⇒ Q` with store `E = F` (ECTR5) / `F = E`
   (ECTR6) and ¬(P F) where P F = G[E:=F].  Returns (E-var, the equality
   hyp, the ¬-hyp, swapped = ECTR6). *)
let find_ectr56 ctx g =
  let try_dir x y_exp heq swapped =
    let g' = subst_prd [(x, y_exp)] g in
    if g' = g then None
    else
      List.find_map
        (fun (hn, p) ->
           match p with
           | Unary (Not, q) when q = g' -> Some (x, heq, hn, swapped)
           | _ -> None)
        ctx.hyps
  in
  List.find_map
    (fun (he, p) ->
       match p with
       | Eq (Var x, Var y) ->
         (match try_dir x (Var y) he false with
          | Some r -> Some r
          | None -> try_dir y (Var x) he true)
       | Eq (Var x, e2) -> try_dir x e2 he false
       | Eq (e1, Var y) -> try_dir y e1 he true
       | _ -> None)
    ctx.hyps

(* AR4 needs an explicit F with `F ≤ 𝟎` provable in scope.  The replay
   doesn't record F, but `F ≤ 𝟎` is one of the hypotheses PP introduced
   on the way to the leaf — find it and return (F, its hyp name). *)
let find_leq_zero_hyp ctx =
  List.find_map
    (fun (name, p) -> match p with
       | Leq (f, Lit "0") -> Some (f, name)
       | _ -> None) ctx.hyps

(* ---- Alpha + universal-binder-kind-insensitive predicate equality ----

   PP normalisation produces the same propositional content under different
   universal binders — `!` (Bang), `forall` (Forall), `forall2` (Forall2) —
   and with different bound-variable names.  All three map to the single LP
   `!!` (the user aliased `♢`/`♡` to it), so two such predicates have the
   *same* LP type.  Canonicalise to De Bruijn levels and fold the universal
   binders into one kind, then compare structurally.  Used by the INS leaf
   search so a needed conjunct like `!x.¬(⊤ ∧ P x)` matches an in-scope hyp
   written `forall2 y.¬(⊤ ∧ P y)`. *)
let canon_binder = function
  | Bang | Forall | Forall2 -> Forall
  | Exists -> Exists

let rec canon_exp env = function
  | Var s -> (match List.assoc_opt s env with Some n -> Var n | None -> Var s)
  | e -> map_exp (canon_exp env) e

let rec canon_prd depth env = function
  | Lift e -> Lift (canon_exp env e)
  | Unary (op, p) -> Unary (op, canon_prd depth env p)
  | Binary (op, a, b) -> Binary (op, canon_prd depth env a, canon_prd depth env b)
  | Mem (es, e) -> Mem (List.map (canon_exp env) es, canon_exp env e)
  | Eq (a, b) -> Eq (canon_exp env a, canon_exp env b)
  | Leq (a, b) -> Leq (canon_exp env a, canon_exp env b)
  | Rel (op, es) -> Rel (op, List.map (canon_exp env) es)
  | Bind (k, xs, body) ->
    let names = List.mapi (fun i _ -> Printf.sprintf "#%d" (depth + i)) xs in
    let env' = List.map2 (fun x n -> (x, n)) xs names @ env in
    Bind (canon_binder k, names, canon_prd (depth + List.length xs) env' body)

let prd_equiv a b = canon_prd 0 [] a = canon_prd 0 [] b

let find_hyp_by_equiv ctx pred =
  List.find_map
    (fun (name, p) -> if prd_equiv p pred then Some name else None) ctx.hyps

(* ---- Witness + hyp lookup for AXM9 / NRM19 ----

   AXM9 (`P v ⇒ Q`): the antecedent is `P v` for some witness v of
   tuple arity n. The hypothesis we need is `(`!! u, ¬ (⊤ ∧ P u))`.
   Iterate witnesses (each tracking its binder's pp-vars), substitute
   into each candidate hypothesis's `!!` body, compare to `P v`.

   NRM19 (`(`♡ u, ¬ (⊤ ∧ R u)) ⇒ Q`): the binder's vars and body R
   come from the goal. For each witness, substitute and look up `R v`
   directly in hyps. *)

(* AXM9 expects an `!!`-form hypothesis (LP-side `π (`!! u, ¬ (⊤ ∧ P u))`).
   On the PP-AST side, the same propositional content can appear under any
   of the universal binders — `!` (`Bang`), `forall` (`Forall`), or
   `forall2` (`Forall2`) — depending on which normalisation chain produced
   it. Accept all three. *)
let axm9_hyp_shape = function
  | Bind ((Bang | Forall | Forall2), vars,
          Unary (Not, Binary (And, t, p))) when is_true_atom t ->
    Some (vars, p)
  | _ -> None

(* Expand an xs entry into candidate (lp_witness, pp_vars) pairs.
   Whole tuple first, then individual components via prj. *)
let witness_candidates (x_name, x_pp_vars) =
  let whole = (L.Name x_name, x_pp_vars) in
  if List.length x_pp_vars <= 1 then [whole]
  else
    let components = List.mapi (fun i pp_var ->
      (L.App (L.Name "\xe2\xa8\xbe", [L.Name "unit"; prj i (L.Name x_name)]), [pp_var])
    ) x_pp_vars in
    whole :: components


(* First-order match: find a substitution σ over [vars] (the only flexible
   symbols) with `pat[σ] = tgt`.  Used to read an AXM9 witness straight off the
   goal's antecedent when it is a *constant* (`0 ϵ s` matched against the hyp
   body `u ϵ s` gives `u ↦ 0`), which the `ctx.xs` variable search can't do. *)
let match_pattern vars pat_prd tgt_prd : (string * exp) list option =
  let acc = ref [] and ok = ref true in
  let bind v e =
    match List.assoc_opt v !acc with
    | Some e' -> if e' <> e then ok := false
    | None -> acc := (v, e) :: !acc
  in
  let rec me pat tgt =
    if !ok then match pat, tgt with
    | Var v, _ when List.mem v vars -> bind v tgt
    | Var v, Var v' -> if v <> v' then ok := false
    | Var _, _ -> ok := false
    | Lit s, Lit s' -> if s <> s' then ok := false
    (* Every other shape: congruent iff same head, payload, and arity.  Going
       through [exp_congruence] covers the Range/Maplet/Inverse/SetLit/
       DomRestrict/RanRestrict operators the old hand-rolled cases silently
       dropped (`_ -> ok := false`), and is exhaustive so a new constructor
       can't reintroduce that gap. *)
    | _ ->
      (match exp_congruence pat tgt with
       | Some pairs -> List.iter (fun (p, t) -> me p t) pairs
       | None -> ok := false)
  in
  let rec mp pat tgt =
    if !ok then match pat, tgt with
    | Lift e, Lift e' -> me e e'
    | Unary (o, p), Unary (o', p') when o = o' -> mp p p'
    | Binary (o, a, b), Binary (o', a', b') when o = o' -> mp a a'; mp b b'
    | Bind (bd, vs, p), Bind (bd', vs', p') when bd = bd' && vs = vs' -> mp p p'
    | Mem (es, e), Mem (es', e') when List.length es = List.length es' ->
      List.iter2 me es es'; me e e'
    | Eq (a, b), Eq (a', b') -> me a a'; me b b'
    | Leq (a, b), Leq (a', b') -> me a a'; me b b'
    | _ -> ok := false
  in
  mp pat_prd tgt_prd;
  if !ok then Some (List.rev !acc) else None

let find_axm9_match ctx goal =
  match antecedent_of goal with
  | None -> None
  | Some p_v ->
    let try_candidate (lp_witness, pp_vars) (h_name, h_pred) =
      match axm9_hyp_shape h_pred with
      | Some (h_vars, h_body)
        when List.length h_vars = List.length pp_vars ->
        let env = List.map2 (fun v pp -> (v, Var pp)) h_vars pp_vars in
        if subst_prd env h_body = p_v then Some (lp_witness, h_name)
        else None
      | _ -> None
    in
    let from_xs =
      List.find_map (fun x ->
        List.find_map (fun cand ->
          List.find_map (try_candidate cand) ctx.hyps
        ) (witness_candidates x)
      ) ctx.xs
    in
    match from_xs with
    | Some _ as r -> r
    | None ->
      (* Derive the witness from the antecedent: the universal hyp body
         `R u` matched against `p_v` binds each `u` to the witness component
         (a constant, e.g. `0`/`7`, that no `ctx.xs` var supplies).  Build the
         tuple `unit ⨾ σ(u₀) ⨾ … ⨾ σ(uₙ)`. *)
      let env =
        List.concat_map (fun (x, vs) ->
          List.mapi (fun i v -> (v, L.Proj (i, x))) vs) ctx.xs
      in
      List.find_map (fun (h_name, h_pred) ->
        match axm9_hyp_shape h_pred with
        | Some (h_vars, h_body) ->
          (match match_pattern h_vars h_body p_v with
           | Some sigma when List.length sigma = List.length h_vars ->
             let witness =
               List.fold_left (fun acc v ->
                 L.App (L.Name "\xe2\xa8\xbe",
                        [acc; L.Exp (env, List.assoc v sigma)]))
                 (L.Name "unit") h_vars
             in
             Some (witness, h_name)
           | _ -> None)
        | None -> None) ctx.hyps

let find_nrm19_match ctx goal =
  match goal with
  | Binary (Imp, Bind (Forall2, vars, Unary (Not, Binary (And, t, r_body))), _)
    when is_true_atom t ->
    let try_candidate (lp_witness, pp_vars) =
      if List.length pp_vars <> List.length vars then None
      else
        let env = List.map2 (fun v pp -> (v, Var pp)) vars pp_vars in
        let needed = subst_prd env r_body in
        match find_hyp_by_pred ctx needed with
        | Some h_name -> Some (lp_witness, h_name)
        | None -> None
    in
    List.find_map (fun x ->
      List.find_map try_candidate (witness_candidates x)
    ) ctx.xs
  | _ -> None

(* ---- INS: universal-instantiation contradiction search ----

   INS arises when PP's instantiation phase discovers that universal
   hypotheses in H, together with simple hypotheses, form a
   contradiction.  The replay child is always AXM7 (⊥ ⇒ ⊥) —
   redundant once we have the evidence.

   Evidence term:  !!_to_pi _ h_univ witness (∧ᵢ h₁ … hₙ)
   where h_univ is a normalised universal  ∀x · ¬(P₁(x) ∧ … ∧ Pₙ(x)),
   witness is a tuple variable, and each hᵢ matches Pᵢ(witness).

   Generalises find_axm9_match from "one non-trivial conjunct after ⊤"
   to "N conjuncts, all matched".  *)

let ins_hyp_shape = function
  | Bind (binder, vars, Unary (Not, body)) when binder = Bang || binder = Forall || binder = Forall2 ->
    Some (binder, vars, body)
  | _ -> None

let collect_conj_leaves = Pp_lp.conj_leaves

(* ---- On-the-fly equality proofs for reordered arithmetic conjuncts ----

   PP's solver records the hypotheses behind an INS leaf in its own term
   order: the universal reads `x - g ≤ 𝟎`, the in-scope hyp reads
   `(—g) + x ≤ 𝟎`.  Same value, but `find_hyp_by_equiv` is structural and
   misses it.  Rather than `trust` the conjunct, we build a real proof that
   the two sides are equal (a permutation of one signed sum) by reflecting onto
   `to_int` (Stdlib.Z), where the reorder is `+_com`/`+_assoc` and `—` distributes,
   and transport the hypothesis along it with `leq_subst_l`. *)

(* The projection env (witness tuple-var → `prj k x`) the printer needs, built
   from the in-scope binders; mirrors [Rule_emit.pp_env_of]. *)
let proj_env_of_ctx ctx : L.proj_env =
  List.concat_map (fun (x_name, pp_vars) ->
    List.mapi (fun i v -> (v, L.Proj (i, x_name))) pp_vars) ctx.xs

(* ---- NRM29 trust-free dispatch: witness + ⊤-normalisation bridge ----

   The (post-AR3_F) NRM29 goal is `(♡(d,rest…)·¬⋀(bounds)) ⇒ R` where the
   solver pins the leading binder `d` (the `prj 0` slot) so the two cancelling
   bounds `d + r ≤ 𝟎`, `—d − r ≤ 𝟎` both vanish.  `NRM29` (Nrm.lp) peels `d`
   by instantiating at the witness `b`, leaving the premise
   `♢v'·¬⋀(ps (v' ⨾ b v')) ⇒ R` with the substituted bounds *literal*.  PP
   instead ⊤-normalises them, so the replay continuation proves `♢v'·¬⊤ ⇒ R`.
   We bridge the two: a congruence proof `⋀(substituted) = ⊤` (each cancelling
   bound `= ⊤` via `eq_true` + `leq_zero_of_sum_zero` + `prove_sum_zero`).

   Returns `(b, cong)`: the witness `λ v', <w>` and the congruence proof
   `((♢v'·¬⋀ subst) ⇒ R) = ((♢v'·¬⊤) ⇒ R)` (the caller transports with
   `=⇒ (eq_sym cong)`).  None if the goal isn't this cancelling-bounds shape. *)
let nrm29_witness_bridge ctx goal : (L.term * L.term) option =
  let opt_all xs =
    if List.for_all Option.is_some xs then Some (List.map Option.get xs) else None
  in
  match flatten_binds goal with
  | Binary (Imp, Bind (Forall2, d :: rest, Unary (Not, conj)), _) ->
    let bounds = Pp_lp.conj_children_left conj in
    let bound_lhss =
      List.filter_map (function Leq (e, Lit "0") -> Some e | _ -> None) bounds in
    if List.length bound_lhss <> List.length bounds then None
    else
      (* witness pins `d`: take a bound `d + r ≤ 𝟎` (d with coeff +1), drop the
         `d` monomial, negate the rest → `w` (an expr over the remaining vars). *)
      let witness_of e =
        match flatten_signed e with
        | Some atoms when List.mem (Var d, 1) atoms ->
          let rec drop_d = function
            | (Var x, 1) :: tl when x = d -> tl
            | a :: tl -> a :: drop_d tl
            | [] -> []
          in
          let rest_neg = List.map (fun (a, s) -> (a, -s)) (drop_d atoms) in
          Some (lfold_exp rest_neg)
        | _ -> None
      in
      (match List.find_map witness_of bound_lhss with
       | None -> None
       | Some w ->
         (* remaining binder vars → `prj k` of a tuple var (after dropping d). *)
         let env_of v = List.mapi (fun k x -> (x, L.Proj (k, v))) rest in
         let vb = fresh_x_local ctx in
         let b_term = L.Lambda (vb, None, L.Exp (env_of vb, w)) in
         (* per-bound `(lhs[d:=w] ≤ 𝟎) = ⊤`, rendered over a fresh bridge var. *)
         let vc = fresh_x_local ctx in
         let env_c = env_of vc in
         let eqtrue_of lhs =
           let lhs_sub = subst_exp [ (d, w) ] lhs in
           Option.map
             (fun eqzero ->
                L.App (L.Name "eq_true",
                  [ L.Hole;
                    L.App (L.Name "leq_zero_of_sum_zero", [ L.Hole; eqzero ]) ]))
             (prove_sum_zero env_c lhs_sub)
         in
         (* Register the bridge tuple `vc` in ctx.xs (not just env_c) so a
            generated `prove_sum_zero` under here can resolve a bound var's
            `ϵ INT` evidence to its `_it_n_k vc` premise (cf. ar3f_cong). *)
         (match with_x ctx vc rest (fun () -> opt_all (List.map eqtrue_of bound_lhss)) with
          | None -> None
          | Some [] -> None
          | Some eqtrues ->
            (* `⋀(∎ ∷ c1 ∷ … ∷ ck) = ⊤`: peel the last conjunct (reduces the
               `⋀ (_ ∷ ⊤)` away), recurse on the prefix.  Singleton ≡ c1. *)
            let rec list_eq = function
              | [] -> assert false
              | [ et ] -> et
              | ets ->
                let last = List.nth ets (List.length ets - 1) in
                let init = List.filteri (fun i _ -> i < List.length ets - 1) ets in
                L.App (L.Name "eq_trans",
                  [ L.App (L.Name "conj_snoc_last_cong", [ last ]); list_eq init ])
            in
            let body = L.Lambda (vc, None, L.App (L.Name "not_cong", [ list_eq eqtrues ])) in
            let cong = L.App (L.Name "imp_cong_l", [ L.App (L.Name "!!_cong", [ body ]) ]) in
            Some (b_term, cong)))
  | _ -> None

(* A hyp `h_lhs ≤ 𝟎` that is a term-reordering of [lhs ≤ 𝟎]. *)
let find_leq_reorder ctx lhs =
  match flatten_signed lhs with
  | None -> None
  | Some fl ->
    let key = List.sort compare fl in
    List.find_map (fun (name, p) -> match p with
      | Leq (h_lhs, Lit "0") ->
        (match flatten_signed h_lhs with
         | Some fh when List.sort compare fh = key -> Some (name, h_lhs)
         | _ -> None)
      | _ -> None) ctx.hyps

(* Equality-store bridge: [needed] isn't in scope directly, but rewriting a
   bare-identifier side `v` of an in-scope equality hyp to its other side
   maps some in-scope hyp H onto it (H[v:=other] ≡ needed, alpha).  Transport
   H along the equality with `ind_eq (other = v) (λ z, H[v:=z]) h`.  This is
   how PP's equality prover (EGALITE, ch. 9) discharges goals: hypotheses are
   matched modulo the stored equalities. *)
let eq_rewrite_evidence ctx needed =
  let render_env = proj_env_of_ctx ctx in
  let transport heq_name ~sym v hyp_name hyp_pred =
    let z = fresh_x_local ctx in
    let motive =
      L.Lambda (z, Some L.Tau_i,
        L.Pred (render_env, subst_prd [ (v, Var z) ] hyp_pred))
    in
    let eqt =
      if sym then L.App (L.Name "eq_sym", [ L.Name heq_name ])
      else L.Name heq_name
    in
    L.App (L.Name "ind_eq", [ eqt; motive; L.Name hyp_name ])
  in
  List.find_map (fun (heq_name, p) ->
    match p with
    | Eq (lhs, rhs) when lhs <> rhs ->
      (* [~sym]: ind_eq wants π (other = v); heq : π (v = other) needs
         eq_sym, heq : π (other = v) is direct. *)
      let try_var_side v other ~sym =
        List.find_map (fun (h, hp) ->
          if h = heq_name || prd_equiv hp needed then None
          else
            let hp' = subst_prd [ (v, other) ] hp in
            if prd_equiv hp' needed
            then Some (transport heq_name ~sym v h hp)
            else
              (* literal-fold bridge: the substitution leaves a foldable sum
                 (`1 − (0+0)` where PP recorded `1`) — transport, then close
                 the gap with a generated sum equality. *)
              match needed, hp' with
              | Leq (nl, Lit "0"), Leq (hl, Lit "0") ->
                Option.map
                  (fun eqpf ->
                     L.App (L.Name "leq_subst_l",
                            [ eqpf; transport heq_name ~sym v h hp ]))
                  (prove_sum_eq render_env nl hl)
              | _ -> None) ctx.hyps
      in
      let a = match lhs with
        | Var v -> try_var_side v rhs ~sym:true
        | _ -> None
      in
      (match a with
       | Some _ as r -> r
       | None ->
         match rhs with
         | Var v -> try_var_side v lhs ~sym:false
         | _ -> None)
    | _ -> None) ctx.hyps

let leaf_evidence ctx env leaf =
  if is_true_atom leaf then Some true_intro
  else
    let needed = subst_prd env leaf in
    (* Match up to alpha + universal-binder kind: a conjunct may be a
       universal (e.g. the "no image" `!x.¬(⊤ ∧ …)` of a totality goal)
       whose in-scope hyp uses a different binder/var but the same LP type. *)
    match find_hyp_by_equiv ctx needed with
    | Some h -> Some (L.Name h)
    | None ->
      (* arithmetic-reorder bridge: PP recorded the conjunct in a different
         term order than the universal.  Prove `needed = hyp` and transport. *)
      let reorder =
        match needed with
        | Leq (lhs, Lit "0") ->
          (match find_leq_reorder ctx lhs with
           | Some (h, h_lhs) ->
             (match prove_sum_eq (proj_env_of_ctx ctx) lhs h_lhs with
              | Some eqpf ->
                Some (L.App (L.Name "leq_subst_l", [ eqpf; L.Name h ]))
              | None -> None)
           | None -> None)
        | _ -> None
      in
      (match reorder with
       | Some _ as r -> r
       | None -> eq_rewrite_evidence ctx needed)

(* The eliminator that instantiates a normalised universal at a witness: `!!`,
   `♢`, `♡` all alias one `!!` but keep distinct elim lemmas (lemmas/Tuple.lp). *)
let elim_of_binder = function
  | Bang -> "!!_to_pi"
  | Forall -> "\xe2\x99\xa2_to_pi"   (* ♢_to_pi *)
  | Forall2 -> "\xe2\x99\xa1_to_pi"  (* ♡_to_pi *)
  | Exists -> failwith "Exists binder in ins_hyp_shape"

(* Witness terms PP synthesises rather than binds, harvested from the hyps for
   the INS search: every B-function application (`App`/`EApp`) — the image `f(a)`
   of an earlier witness, for `∀y·¬(y∈t ∧ ¬(y∈u))` instantiated at `f(a)` — and
   every integer literal (`Lit`) — the bound a range-membership universal is
   instantiated at, e.g. `16` from the goal `16 ϵ 0..255`.  Plus the variables of
   an expression (to keep an applied term over in-scope witness vars). *)
let rec apps_of_exp acc e =
  let acc = match e with App _ | EApp _ -> e :: acc | _ -> acc in
  fold_exp apps_of_exp acc e

let rec lits_of_exp acc e =
  let acc = match e with Lit _ -> e :: acc | _ -> acc in
  fold_exp lits_of_exp acc e

(* [of_exp]'s hits over every expression in a predicate (recursively). *)
let exps_of_prd of_exp p =
  let rec go acc = function
    | Lift e -> of_exp acc e
    | Unary (_, q) -> go acc q
    | Binary (_, a, b) -> go (go acc a) b
    | Mem (es, e) -> List.fold_left of_exp (of_exp acc e) es
    | Eq (a, b) | Leq (a, b) -> of_exp (of_exp acc a) b
    | Rel (_, es) -> List.fold_left of_exp acc es
    | Bind (_, _, body) -> go acc body
  in go [] p

let apps_of_prd = exps_of_prd apps_of_exp
let lits_of_prd = exps_of_prd lits_of_exp

let rec vars_of_exp acc = function
  | Var v -> v :: acc
  | e -> fold_exp vars_of_exp acc e

(* The native-int value of a *ground* `+`/`−` expression (every atom a parseable
   literal); None if any atom is symbolic or a literal too big to fold.  Lets the
   INS search decide a ground bound `e ≤ 𝟎` holds before emitting its proof. *)
let ground_value e =
  match flatten_signed e with
  | None -> None
  | Some atoms ->
    List.fold_left (fun acc (a, s) ->
      match acc, a with
      | Some c, Lit l -> Option.map (fun n -> c + s * n) (int_of_string_opt l)
      | _ -> None) (Some 0) atoms

let find_ins_contradiction ctx =
  let proj_env = proj_env_of_ctx ctx in
  (* ---- forward+backward saturating instantiation search ----

     A single `[INS]` (or a `FIN_INS` chain PP writes out explicitly) can hide a
     *multi-step* contradiction: `x∈s`, `s⊆t`, `t⊆u`, `x∉u` is inconsistent only
     after deriving `x∈t` (modus ponens on `s⊆t`).  Saturate: instantiate each
     universal hyp `!!v·¬⋀(P₁…Pₙ)` at each in-scope witness; once every conjunct
     matches a hyp or an already-derived fact, that universal closes ⊥ (the
     terminal).  When exactly one conjunct Pⱼ is missing, derive its negation as
     a new fact and retry.  Deriving ¬Pⱼ from the rest covers both directions: a
     missing `¬B` yields `B` (forward MP, via `¬¬ₑ`), a missing positive `A`
     yields `¬A` (backward MT, a bare λ).  [pool] holds the derived
     `(pred, evidence)` facts, pred already substituted over the witness vars. *)
  let match_leaf pool env leaf =
    let needed = subst_prd env leaf in
    let from_pool () =
      List.find_map (fun (p, t) -> if prd_equiv p needed then Some t else None) pool in
    (* a trivially-true bound `e ≤ 𝟎`, proved rather than matched to a hyp.  Two
       shapes: a *ground* non-positive `e` (e.g. `−16`, `16−255`, from a range
       universal instantiated at a literal — `to_int e ≤ 0` COMPUTES in Stdlib.Z,
       closed by `le_intro _ _ (λ h, h)`); or a symbolic `e` that sums to zero
       (`x − x`, a min/max instantiation — the reflective `prove_sum_zero`). *)
    let arith () = match needed with
      | Leq (e, Lit "0") ->
        (match ground_value e with
         | Some c when c <= 0 ->
           Some (L.App (L.Name "le_intro",
             [ L.Exp (proj_env, e); L.Name "\xf0\x9d\x9f\x8e" (* 𝟎 *);
               L.Lambda ("_h", None, L.Name "_h") ]))
         | _ ->
           Option.map
             (fun pf -> L.App (L.Name "leq_zero_of_sum_zero", [L.Hole; pf]))
             (prove_sum_zero proj_env e))
      | _ -> None
    in
    match needed with
    (* a refuted existential `∃x·g(x)=c` instantiates at the witness to the
       reflexive `c=c` — discharged by `eq_refl`, not any hyp.  (xst_app etc.) *)
    | Eq (a, b) when a = b -> Some (eq_refl (L.Exp (proj_env, a)))
    | _ ->
      match leaf_evidence ctx env leaf with
      | Some _ as r -> r
      | None ->
        match from_pool () with
        | Some _ as r -> r
        | None -> arith ()
  in
  (* (elim, h_name, witness, env, leaves, per-leaf evidence) for one
     (universal hyp × witness) against [pool]; None on shape/arity mismatch.
     A candidate's [pp_exps] are the expressions its tuple slots stand for (a
     bound var `Var v`, or an applied term `f(a)`); [env] substitutes them for
     the universal's binder vars. *)
  let classify pool (lp_witness, pp_exps) (h_name, h_pred) =
    match ins_hyp_shape h_pred with
    | Some (binder, h_vars, h_body)
      when List.length h_vars = List.length pp_exps ->
      let env = List.map2 (fun v e -> (v, e)) h_vars pp_exps in
      let leaves = collect_conj_leaves h_body in
      let evs = List.map (match_leaf pool env) leaves in
      Some (elim_of_binder binder, h_name, lp_witness, env, leaves, evs)
    | _ -> None
  in
  (* Witness atoms: each is an `(lp-term, exp)` standing for one tuple slot — a
     binder projection `(prj i x, Var pp)`, or an applied term `(f(a), f(a))`
     drawn from the hyps over in-scope witness vars.  PP instantiates a universal
     at the image `f(a)` of an earlier witness (composition chains), and may
     split a `forall2(x,y)` witness across two 1-tuple binders, so a slot can be
     either; [products] assembles them into N-tuples. *)
  let ppset = List.concat_map snd ctx.xs in
  let applied_terms =
    List.concat_map (fun (_, p) -> apps_of_prd p) ctx.hyps
    |> List.sort_uniq compare
    |> List.filter (fun e ->
         let vs = vars_of_exp [] e in
         vs <> [] && List.for_all (fun v -> List.mem v ppset) vs)
  in
  (* literal witnesses: each integer literal in the hyps (the `N` of a goal-side
     `¬(N ϵ S)`).  A range-membership universal `∀x·¬((lo≤x ∧ x≤hi) ∧ ¬(x∈S))`
     instantiated at `N` discharges to the ground bounds + the `¬(N∈S)` hyp — the
     apero `N ϵ 0..hi` register-width checks, where no witness is in scope. *)
  let lit_terms =
    List.concat_map (fun (_, p) -> lits_of_prd p) ctx.hyps
    |> List.sort_uniq compare
  in
  let atoms =
    List.concat_map (fun (x_name, x_pp_vars) ->
      List.mapi (fun i pp -> (prj i (L.Name x_name), Var pp)) x_pp_vars) ctx.xs
    @ List.map (fun e -> (L.Exp (proj_env, e), e)) applied_terms
  in
  let rec products n =
    if n <= 0 then [ [] ]
    else List.concat_map
           (fun a -> List.map (fun rest -> a :: rest) (products (n - 1))) atoms
  in
  let build_witness atom_list =
    (* slot #i lands at the tuple position counted from the right (NRM8/9
       take/drop; `prj 0 (… ⨾ x) ↪ x`), so fold the atoms reversed; the exps
       stay in PP-binder order for [classify]'s env. *)
    let tup = List.fold_left
      (fun acc (e, _) -> L.App (L.Name "\xe2\xa8\xbe", [ acc; e ]))
      (L.Name "unit") (List.rev atom_list) in
    (tup, List.map snd atom_list)
  in
  (* the arities that some universal hyp actually needs — only build composites
     for those (≥2; arity 1 is the single-binder / arity-1 applied candidates). *)
  let arities =
    List.sort_uniq compare
      (List.filter_map (fun (_, p) ->
         match ins_hyp_shape p with
         | Some (_, vs, _) -> Some (List.length vs)
         | None -> None) ctx.hyps)
  in
  (* applied terms and literals both instantiate a 1-var universal at a synthesised
     `unit ⨾ <term>` tuple. *)
  let synth_cands =
    List.map (fun e ->
      (L.App (L.Name "\xe2\xa8\xbe", [L.Name "unit"; L.Exp (proj_env, e)]), [e]))
      (applied_terms @ lit_terms)
  in
  (* The old search built *every* `products n` = |atoms|^N composite N-tuple and
     classified each — exponential in N, so a length-k relational composition
     (whose universal has arity k) timed out past k ≈ 6.  Keep that enumeration
     only while it is cheap (a no-regression safety net for the small composites
     that already worked), bounded by [products_cap]; larger arities fall to the
     E-matching below.  [pow_le b e c] tests `bᵉ ≤ c` without overflowing. *)
  let pow_le base exp cap =
    let rec go acc i =
      if i = 0 then acc <= cap
      else if acc > cap then false
      else go (acc * base) (i - 1)
    in go 1 exp
  in
  let products_cap = 4096 in
  let small_products =
    List.concat_map
      (fun n ->
        if n >= 2 && pow_le (List.length atoms) n products_cap
        then List.map build_witness (products n) else [])
      arities
  in
  (* Pool-independent candidates — single-/whole-binder tuples, the bounded
     `products` enumeration, and the synthesised applied/literal tuples — paired
     with every hyp ([classify] rejects an arity mismatch).  These don't change as
     the saturation pool grows, so build them once. *)
  let base_pairs =
    let candidates =
      List.concat_map (fun x ->
        List.map (fun (t, vs) -> (t, List.map (fun v -> Var v) vs))
          (witness_candidates x)) ctx.xs
      @ small_products
      @ synth_cands
    in
    List.concat_map (fun w -> List.map (fun h -> (w, h)) ctx.hyps) candidates
  in
  (* ---- E-matching: unification-guided composite-witness discovery ----

     Rather than enumerate all |atoms|^N tuples and test each, read the witness
     off the hypotheses the way an SMT solver instantiates a quantifier
     (E-matching): match the universal's conjuncts against the in-scope facts
     (hyps + the derived pool), solving for the binder vars.  For
     `!!(x$2,x$3,x$4)·¬((x0,x$4):r1 ∧ (x$4,x$3):r2 ∧ (x$3,x$2):r3 ∧ (x$2,x4):r4)`,
     `(x0,x$4):r1` matched against hyp `(x0,x1):r1` pins `x$4 := x1`, then
     `(x$4,x$3):r2 = (x1,x$3):r2` against `(x1,x2):r2` pins `x$3 := x2`, and so on
     — the witness for a length-k chain falls out in O(leaves × facts × vars),
     linear in k rather than |atoms|^k.  A conjunct that matches no fact
     (arithmetic-trivial, reflexive, or the one gap of a saturation step) is left
     for [classify] / the saturation loop; a binder var only such a conjunct
     constrains stays unbound and is filled from [atoms] (the residual
     enumeration — empty for a fully relational chain). *)
  let ematch h_vars leaves facts =
    (* [spec] caps speculative skips of a conjunct that *did* match a fact (needed
       only if that conjunct is alternatively dischargeable by arithmetic at a
       different binding); a conjunct matching no fact is skipped for free. *)
    let rec go sigma spec = function
      | [] -> [ sigma ]
      | leaf :: rest ->
        let leaf' = subst_prd sigma leaf in
        let free = List.filter (fun v -> not (List.mem_assoc v sigma)) h_vars in
        let exts =
          List.filter_map (fun fact ->
            match match_pattern free leaf' fact with
            | Some ext -> Some (sigma @ ext)
            | None -> None) facts
          |> List.sort_uniq compare
        in
        if exts = [] then go sigma spec rest
        else
          List.concat_map (fun s -> go s spec rest) exts
          @ (if spec > 0 then go sigma (spec - 1) rest else [])
    in
    go [] 1 leaves |> List.sort_uniq compare
  in
  (* residual enumeration of the binder vars E-matching left unbound, over
     [atoms]; bounded by [products_cap] so a universal no fact constrains can't
     reintroduce the |atoms|^N blow-up. *)
  let rec products_over = function
    | [] -> [ [] ]
    | v :: rest ->
      List.concat_map (fun (_, e) ->
        List.map (fun tl -> (v, e) :: tl) (products_over rest)) atoms
  in
  (* the (E-matched composite witness, source universal hyp) pairs for one
     saturation round, re-derived each round because the pool grows. *)
  let composite_pairs pool =
    let facts = List.map snd ctx.hyps @ List.map fst pool in
    List.concat_map (fun (h_name, h_pred) ->
      match ins_hyp_shape h_pred with
      | Some (_, h_vars, h_body) when List.length h_vars >= 2 ->
        let leaves = collect_conj_leaves h_body in
        List.concat_map (fun sigma ->
          let unbound =
            List.filter (fun v -> not (List.mem_assoc v sigma)) h_vars in
          if not (pow_le (List.length atoms) (List.length unbound) products_cap)
          then []
          else
            List.map (fun fill ->
              let full = sigma @ fill in
              let atom_list =
                List.map (fun v ->
                  let e = List.assoc v full in (L.Exp (proj_env, e), e)) h_vars
              in
              (build_witness atom_list, (h_name, h_pred)))
              (products_over unbound))
          (ematch h_vars leaves facts)
      | _ -> []) ctx.hyps
  in
  let unmatched_count (_, _, _, _, _, evs) =
    List.length (List.filter Option.is_none evs) in
  let rec none_index i = function
    | [] -> assert false
    | None :: _ -> i
    | Some _ :: tl -> none_index (i + 1) tl
  in
  (* terminal: every conjunct matched → instantiate the universal to ⊥. *)
  let terminal (elim, h_name, witness, _env, _leaves, evs) =
    L.Refine (L.Name elim,
      [L.Hole; L.Name h_name; witness; conj_chain (List.map Option.get evs)])
  in
  (* the fact a one-gap universal derives: the `¬¬`-collapsed negation of the
     missing conjunct (`¬B` → `B`; positive `A` → `¬A`). *)
  let derived_pred env pj =
    match pj with
    | Unary (Not, b) -> subst_prd env b
    | _ -> Unary (Not, subst_prd env pj)
  in
  (* and its evidence term: the universal instantiated to ⊥ with a fresh `hj`
     assumed at the gap slot, abstracted back out (and `¬¬ₑ`-eliminated when the
     gap was a negation, so the result is the positive fact). *)
  let derive (elim, h_name, witness, env, leaves, evs) j =
    ctx.n <- ctx.n + 1;
    let hj = Printf.sprintf "_h%d" ctx.n in
    let pj = List.nth leaves j in
    let conj_ev = conj_chain
      (List.mapi (fun k ev -> if k = j then L.Name hj else Option.get ev) evs) in
    let inner = L.App (L.Name elim, [L.Hole; L.Name h_name; witness; conj_ev]) in
    let lam =
      L.Lambda (hj, Some (L.Pi_pred (proj_env, subst_prd env pj)), inner) in
    match pj with
    | Unary (Not, b) ->
      L.App (L.Name "\xc2\xac\xc2\xac\xe2\x82\x91"  (* ¬¬ₑ *),
             [L.Pred (proj_env, subst_prd env b); lam])
    | _ -> lam
  in
  let is_new pool pred = not (List.exists (fun (p, _) -> prd_equiv p pred) pool) in
  let rec saturate pool fuel =
    if fuel <= 0 then None
    else
      let pairs = base_pairs @ composite_pairs pool in
      let cs = List.filter_map (fun (w, h) -> classify pool w h) pairs in
      match List.find_opt (fun c -> unmatched_count c = 0) cs with
      | Some c -> Some (terminal c)
      | None ->
        let step =
          List.find_map (fun c ->
            if unmatched_count c <> 1 then None
            else
              let (_, _, _, env, leaves, evs) = c in
              let j = none_index 0 evs in
              let pred = derived_pred env (List.nth leaves j) in
              if is_new pool pred then Some (c, j, pred) else None
          ) cs
        in
        match step with
        | Some (c, j, pred) -> saturate ((pred, derive c j) :: pool) (fuel - 1)
        | None -> None
  in
  saturate [] 32

(* ---- ARITH: the ctx side of the Farkas contradiction search ----
   Extract the in-scope `e ≤ 𝟎` hypotheses (with their signed-atom vectors);
   the certificate search itself is ctx-free and lives in
   [Arith_proofs.find_arith_contradiction] (Fourier–Motzkin elimination, which
   bounds its own blowup).  The cap here is just a sanity bound on how many
   hypotheses to feed it — generous enough for a long telescoping chain. *)
let arith_max_hyps = 32

let arith_leq_hyps ctx =
  let all =
    List.filter_map (fun (name, p) -> match p with
      | Leq (e, Lit "0") ->
        (match flatten_signed e with
         | Some atoms -> Some (name, e, atoms)
         | None -> None)
      | _ -> None) ctx.hyps
  in
  (* most-recent-first; bound the number of hypotheses folded *)
  List.filteri (fun i _ -> i < arith_max_hyps) all

(* Thin ctx wrapper: pull the in-scope `≤ 𝟎` hypotheses, then hand the
   projection env + hyp list to the (ctx-free) certificate search. *)
let find_arith_contradiction ctx =
  Arith_proofs.find_arith_contradiction (proj_env_of_ctx ctx) (arith_leq_hyps ctx)

let arith_diagnostic ctx =
  let hyps = arith_leq_hyps ctx in
  let b = Buffer.create 128 in
  Buffer.add_string b "  ≤-hypotheses considered (most recent first):";
  if hyps = [] then Buffer.add_string b " (none)"
  else
    List.iter (fun (n, e, _) ->
      Buffer.add_string b
        (Printf.sprintf "\n    %s : %s" n (Emit_pp.prd_to_pp (Leq (e, Lit "0")))))
      hyps;
  Buffer.contents b

(* Diagnostic for a failed [find_ins_contradiction], built from the same
   predicates the search uses so it reports exactly why no (hyp × witness)
   discharged the contradiction: the hypotheses and witnesses in scope, and
   for each universal hyp the witness leaving the fewest unmatched conjuncts
   together with which conjuncts those are (rendered in PP syntax). *)
let ins_diagnostic ctx =
  let b = Buffer.create 256 in
  let add fmt = Printf.ksprintf (Buffer.add_string b) fmt in
  let hyps = List.rev ctx.hyps and xs = List.rev ctx.xs in
  add "  hypotheses in scope (%d):" (List.length hyps);
  if hyps = [] then add " (none)"
  else List.iter (fun (h, p) -> add "\n    %s : %s" h (Emit_pp.prd_to_pp p)) hyps;
  add "\n  witnesses in scope (%d binder%s):"
    (List.length xs) (if List.length xs = 1 then "" else "s");
  if xs = [] then add " (none — INS reached outside any quantifier binder)"
  else List.iter (fun (x, vs) -> add "\n    %s \xe2\x86\xa6 [%s]" x (String.concat ", " vs)) xs;
  let univ =
    List.filter_map (fun (h, p) ->
      match ins_hyp_shape p with
      | Some (_, vars, body) -> Some (h, vars, body)
      | None -> None) hyps
  in
  (match univ with
   | [] ->
     add "\n  no in-scope hypothesis has the universal form \
          `\xe2\x88\x80x.\xc2\xac(\xe2\x80\xa6)` that INS instantiates"
   | _ ->
     add "\n  universal hyps examined (closest witness per hyp):";
     List.iter (fun (h, vars, body) ->
       let leaves = collect_conj_leaves body in
       let attempts =
         List.concat_map witness_candidates xs
         |> List.filter_map (fun (_w, pp_vars) ->
              if List.length vars <> List.length pp_vars then None
              else
                let env = List.map2 (fun v pp -> (v, Var pp)) vars pp_vars in
                let missing =
                  List.filter
                    (fun l -> not (is_true_atom l) && leaf_evidence ctx env l = None)
                    leaves
                in
                Some (pp_vars, env, missing))
       in
       match
         List.sort (fun (_, _, a) (_, _, c) ->
           compare (List.length a) (List.length c)) attempts
       with
       | [] ->
         add "\n    %s : binds %d var(s); no in-scope witness has that arity"
           h (List.length vars)
       | (pp_vars, env, missing) :: _ ->
         add "\n    %s with witness [%s]: %d/%d conjunct(s) unmatched"
           h (String.concat ", " pp_vars) (List.length missing) (List.length leaves);
         List.iter (fun l ->
           add "\n        \xe2\x9c\x97 %s" (Emit_pp.prd_to_pp (subst_prd env l)))
           missing)
       univ);
  Buffer.contents b
