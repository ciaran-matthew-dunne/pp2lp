(* Arithmetic proof synthesis — the ctx-free half of the emitter's solver
   bridge, split out of [Emit_ctx] (move-only).  Everything here takes a
   projection env and PP expressions / signed-atom lists, never the mutable
   [ctx]: signed-atom normalisation, additive cancellation, the sum-equality
   and positivity provers, and the Farkas linear-combination contradiction.
   [Emit_ctx] keeps the ctx-side wrappers (hyp extraction; witness / INS /
   equality-store searches). *)

open Syntax_pp

module L = Lp_tree

let is_atom_exp = function
  | Var _ | Nat _ | BigNat _ | App _ | EApp _ | SetOp _ | SetImage _ | Inter _
  | Union _ | Range _ | Maplet _ | Inverse _ | SetLit _ | DomRestrict _
  | RanRestrict _ | BoolOf _ | Compr _ -> true
  | AOp _ | Neg _ -> false

(* A literal is a single folded atom — never unfolded to a `𝟏`-sum (that legacy
   apparatus existed only because the pre-Z encoding couldn't compute; now
   `Stdlib.Z` reduces ground arithmetic).  PP's solver-side folding (`2 + 3 → 5`)
   is matched by [fold_lit_run], which combines a contiguous run of literal atoms
   into one `from_int` via `lit_add`/`lit_neg`, letting ℤ compute the sum.

   Only `Nat` literals fold: they fit OCaml's native `int` by construction, so
   the net value needs no bignum.  A `BigNat` (apero's 2⁶⁴ bounds) is left as an
   opaque atom — compared structurally, never summed — so [is_foldable_lit] is
   false for it and [atom_compare] keeps it among the symbolic atoms. *)
let is_foldable_lit = function Nat _ -> true | _ -> false

(* Sort order for signed atoms: foldable `Nat` literals LAST (so a sum's literal
   part is a contiguous trailing suffix that [fold_lit_run] can collapse), every
   other atom first in structural order.  Sign is the final key component so a
   cancelling pair `(a,−1),(a,+1)` stays adjacent in that order — [prove_cancel]
   relies on the `—a` before `a` orientation (`neg_add`). *)
let atom_compare (a1, s1) (a2, s2) =
  compare ((if is_foldable_lit a1 then 1 else 0), a1, s1)
          ((if is_foldable_lit a2 then 1 else 0), a2, s2)

(* A non-negative PP literal as a bare `Stdlib.Z.ℤ` decimal term.  The emitted
   file is ℤ-global (`Int` opens `Stdlib.Z`), so the decimal parses as a ℤ and
   `Stdlib.Z` computes ground arithmetic on it — replacing the old binary
   `Stdlib.Pos`/`Stdlib.Z.Zpos` construction.  Matches the printer's literals
   (`Pp_lp.pp_from_int`). *)
let z_dec (decimal : string) : L.term = L.Name decimal

(* `ϵ INT` evidence for a τ ι *atom* (a bound tuple slot / free integer var):
   an injected typing premise.  The only ctx-dependent part of [int_evidence],
   so it is set once per emission by [Translate] (single-threaded) rather than
   threaded through every arith helper.  ponytail: dynamically-scoped ref over
   one emission; thread it as a param if emission ever goes concurrent. *)
let atom_int_ev : (exp -> L.term) ref =
  ref (fun _ -> failwith "arith_proofs: atom_int_ev unset")

(* `π (e ϵ INT)` for a τ ι expression.  Compound terms are structurally in INT
   (`—`/`+` land in from_int's range; a literal is from_int of a ℤ), so their
   side-conditions discharge without a premise; an atom defers to [atom_int_ev].
   Mirrors the BOOL precedent — morally-true premises, never a postulate. *)
let int_evidence env e : L.term =
  let ex t = L.Exp (env, t) in
  match e with
  | Nat 0 | Neg (Nat 0) -> L.Name "zero_in_int"
  | Nat n -> L.App (L.Name "from_int_in_int", [z_dec (string_of_int n)])
  | BigNat s -> L.App (L.Name "from_int_in_int", [z_dec s])
  | Neg a -> L.App (L.Name "neg_in_int", [ex a])
  | AOp (Add, x, y) -> L.App (L.Name "add_in_int", [ex x; ex y])
  | AOp (Sub, x, y) -> L.App (L.Name "add_in_int", [ex x; ex (Neg y)])
  (* `card(s)` is integer-valued (B typing); discharge via the card_in_int
     postulate rather than searching for an (impossible) typing premise.
     `card(s)` parses as the generic application `App ("card", …)`. *)
  | App ("card", [ s ]) | SetOp ("card", [ s ]) -> L.App (L.Name "card_in_int", [ex s])
  | _ -> !atom_int_ev e

(* Flatten a `+`/`−` expression to its ordered signed-atom list, pushing unary
   `—` down to the atoms (— distributes over + and is involutive); None if a
   non-arithmetic node blocks it.  Mirrors [normalize]'s recursion exactly, so
   a match here is precisely what [normalize] can prove. *)
let rec flatten_signed e : (exp * int) list option =
  let negate = Option.map (List.map (fun (a, s) -> (a, -s))) in
  let app o p = match o, p with Some a, Some b -> Some (a @ b) | _ -> None in
  match e with
  | Nat 0 | Neg (Nat 0) -> Some []
  | _ when is_atom_exp e -> Some [ (e, 1) ]
  | Neg a when is_atom_exp a -> Some [ (a, -1) ]
  | AOp (Add, a, b) -> app (flatten_signed a) (flatten_signed b)
  | AOp (Sub, a, b) -> app (flatten_signed a) (negate (flatten_signed b))
  | Neg (AOp (Add, a, b)) -> app (negate (flatten_signed a)) (negate (flatten_signed b))
  | Neg (AOp (Sub, a, b)) -> app (negate (flatten_signed a)) (flatten_signed b)
  | Neg (Neg a) -> flatten_signed a
  | _ -> None

let signed_exp (a, s) = if s >= 0 then a else Neg a

(* Left-nested sum of a (non-empty) signed-atom list, as a PP expression. *)
let lfold_exp = function
  | [] -> Nat 0
  | s0 :: rest ->
    List.fold_left (fun acc s -> AOp (Add, acc, signed_exp s)) (signed_exp s0) rest

(* π (lfold l = lfold (sorted l)): bubble-sort the signed-atom list, each
   adjacent swap an `add_comm`/`add_assoc` step lifted to its depth. *)
let prove_eq_lnested env l_orig : L.term =
  let ex e = L.Exp (env, e) in
  let refl e = L.App (L.Name "eq_refl", [ ex e ]) in
  let trans p q = L.App (L.Name "eq_trans", [ p; q ]) in
  let sym p = L.App (L.Name "eq_sym", [ p ]) in
  let comm a b = L.App (L.Name "add_comm", [ ex a; ex b ]) in
  let assoc a b c = L.App (L.Name "add_assoc", [ ex a; ex b; ex c ]) in
  let congL b p = L.App (L.Name "add_congL", [ ex b; p ]) in   (* fix right operand *)
  let congR a p = L.App (L.Name "add_congR", [ ex a; p ]) in   (* fix left operand *)
  let prove_swap l k =
    let nth i = List.nth l i in
    let pre = List.filteri (fun i _ -> i < k) l in
    let suf = List.filteri (fun i _ -> i > k + 1) l in
    let a = signed_exp (nth k) and b = signed_exp (nth (k + 1)) in
    let core =
      match pre with
      | [] -> comm a b                                  (* a + b = b + a *)
      | _ ->
        let p = lfold_exp pre in                        (* (p+a)+b = (p+b)+a *)
        trans (assoc p a b) (trans (congR p (comm a b)) (sym (assoc p b a)))
    in
    List.fold_left (fun acc s -> congL (signed_exp s) acc) core suf
  in
  let swap_list l k =
    List.mapi (fun i x -> if i = k then List.nth l (k + 1)
                          else if i = k + 1 then List.nth l k else x) l
  in
  let first_inversion l =
    let rec go i = function
      | x :: (y :: _ as tl) -> if atom_compare x y > 0 then Some i else go (i + 1) tl
      | _ -> None
    in go 0 l
  in
  let rec go l =
    match first_inversion l with
    | None -> refl (lfold_exp l)
    | Some k -> trans (prove_swap l k) (go (swap_list l k))
  in
  go l_orig

(* π (lfold la + lfold lb = lfold (la @ lb)): peel lb's tail, reassociating
   each element onto la with add_assoc (left-fold structure).  An empty side
   is NOT the identity syntactically (`lfold [] ≡ 𝟎`), so those cases close
   with add_zero/zero_add — reachable since literal `𝟎` flattens to no atom. *)
let rec concat env la lb : L.term =
  let ex t = L.Exp (env, t) in
  match la, List.rev lb with
  | _, [] ->
    let a = lfold_exp la in
    L.App (L.Name "add_zero", [ ex a; int_evidence env a ])
  | [], _ ->
    let b = lfold_exp lb in
    L.App (L.Name "zero_add", [ ex b; int_evidence env b ])
  | _, [ _ ] ->
    L.App (L.Name "eq_refl", [ ex (AOp (Add, lfold_exp la, lfold_exp lb)) ])
  | _, last :: front_rev ->
    let front = List.rev front_rev in
    L.App (L.Name "eq_trans",
      [ L.App (L.Name "eq_sym",
          [ L.App (L.Name "add_assoc",
              [ ex (lfold_exp la); ex (lfold_exp front); ex (signed_exp last) ]) ]);
        L.App (L.Name "add_congL", [ ex (signed_exp last); concat env la front ]) ])

(* Normalise [e] to the left-nested sum of its signed atoms, returning the
   atom list and a proof `e = lfold atoms`.  Pushes `—` to the leaves with
   `opp_add`/`neg_neg`; `add_cong`/`concat` reassemble the recursive proofs. *)
let rec normalize env e : ((exp * int) list * L.term) option =
  let ex t = L.Exp (env, t) in
  let refl t = L.App (L.Name "eq_refl", [ ex t ]) in
  let trans p q = L.App (L.Name "eq_trans", [ p; q ]) in
  let cong px py = L.App (L.Name "add_cong", [ px; py ]) in
  let combine lx px ly py =
    (lx @ ly, trans (cong px py) (concat env lx ly))
  in
  match e with
  (* A literal is a single atom (`Nat`/`BigNat`).  `𝟎` contributes NO atom
     (`lfold [] ≡ 𝟎`, refl; `— 𝟎` via neg_zero) — as an opaque atom it would
     block cancellation (`1 − 0` vs `1`).  Folding of literal *runs* (`𝟐 + 𝟑`)
     happens later, in [fold_lit_run], where ℤ computes the sum. *)
  | Nat 0 -> Some ([], refl e)
  | Neg (Nat 0) -> Some ([], L.App (L.Name "neg_zero", []))
  | _ when is_atom_exp e -> Some ([ (e, 1) ], refl e)
  | Neg a when is_atom_exp a -> Some ([ (a, -1) ], refl (Neg a))
  | AOp (Add, x, y) ->
    (match normalize env x, normalize env y with
     | Some (lx, px), Some (ly, py) -> Some (combine lx px ly py)
     | _ -> None)
  | AOp (Sub, x, y) -> normalize env (AOp (Add, x, Neg y))
  | Neg (AOp (Add, x, y)) ->
    (match normalize env (Neg x), normalize env (Neg y) with
     | Some (lx, px), Some (ly, py) ->
       let l, p = combine lx px ly py in
       Some (l, trans (L.App (L.Name "opp_add", [ ex x; ex y ])) p)
     | _ -> None)
  | Neg (AOp (Sub, x, y)) -> normalize env (Neg (AOp (Add, x, Neg y)))
  | Neg (Neg a) ->
    (match normalize env a with
     | Some (la, pa) ->
       Some (la, trans (L.App (L.Name "neg_neg", [ ex a; int_evidence env a ])) pa)
     | None -> None)
  | _ -> None

(* π (lfold l = lfold l') where l' is the SORTED list l with the adjacent
   canceling pair at (k, k+1) — `(a,−1)` then `(a,+1)` — removed.  Cancels
   `—a + a = 𝟎` (`neg_add`) in place, reassociating around the surrounding
   `pre`/`suf`; mirrors [prove_eq_lnested]'s congL-the-suffix structure. *)
let prove_cancel env l k : L.term =
  let ex e = L.Exp (env, e) in
  let trans p q = L.App (L.Name "eq_trans", [ p; q ]) in
  let congL b p = L.App (L.Name "add_congL", [ ex b; p ]) in
  let congR a p = L.App (L.Name "add_congR", [ ex a; p ]) in
  let assoc a b c = L.App (L.Name "add_assoc", [ ex a; ex b; ex c ]) in
  let a = fst (List.nth l k) in
  let pre = List.filteri (fun i _ -> i < k) l in
  let suf = List.filteri (fun i _ -> i > k + 1) l in
  let neg_add_a = L.App (L.Name "neg_add", [ ex a ]) in          (* —a + a = 𝟎 *)
  let fold_congL = List.fold_left (fun acc s -> congL (signed_exp s) acc) in
  match pre with
  | _ :: _ ->
    (* (lfold pre + —a) + a = lfold pre, then congL the suffix back on. *)
    let pf = lfold_exp pre in
    let core = trans (assoc pf (Neg a) a)
                 (trans (congR pf neg_add_a)
                    (L.App (L.Name "add_zero", [ ex pf; int_evidence env pf ]))) in
    fold_congL core suf
  | [] ->
    (match suf with
     | [] -> neg_add_a                                            (* —a + a = 𝟎 = lfold [] *)
     | s0 :: rest ->
       (* (—a + a) + s0 = s0, then congL the rest. *)
       let s0e = signed_exp s0 in
       let core = trans (congL s0e neg_add_a)
                    (L.App (L.Name "zero_add", [ ex s0e; int_evidence env s0e ])) in
       fold_congL core rest)

(* Reduce a SORTED signed-atom list by cancelling adjacent `(a,−1),(a,+1)`
   pairs (same-atom occurrences are contiguous once sorted, signs −1 before
   +1), returning the reduced list and a proof `lfold l = lfold reduced`. *)
let rec reduce_cancel env l : (exp * int) list * L.term =
  let rec find i = function
    | (x, sx) :: ((y, sy) :: _ as tl) ->
      if x = y && sx + sy = 0 then Some i else find (i + 1) tl
    | _ -> None
  in
  match find 0 l with
  | None -> (l, L.App (L.Name "eq_refl", [ L.Exp (env, lfold_exp l) ]))
  | Some k ->
    let l' = List.filteri (fun i _ -> i <> k && i <> k + 1) l in
    let p_step = prove_cancel env l k in
    let r, p_rest = reduce_cancel env l' in
    (r, L.App (L.Name "eq_trans", [ p_step; p_rest ]))

(* ---- Literal-run folding (Stdlib.Z computes the sum) ---- *)

(* A signed foldable literal `(Nat v, s)` rewritten to `from_int <z>` form: the
   ℤ term <z> and a proof `signed_exp (Nat v, s) = from_int z`.  Positive:
   `signed = Nat v` already renders `from_int v`, so `eq_refl`.  Negative:
   `signed = — from_int v`, turned into `from_int (Z.— v)` by `lit_neg`. *)
let signed_to_zform env (v : int) (s : int) : L.term * L.term =
  if s >= 0 then
    (z_dec (string_of_int v),
     L.App (L.Name "eq_refl", [ L.Exp (env, Nat v) ]))
  else
    (L.App (L.Name "Stdlib.Z.\xe2\x80\x94", [ z_dec (string_of_int v) ]),  (* Z.— v *)
     L.App (L.Name "lit_neg", [ z_dec (string_of_int v) ]))

(* Combine two foldable literal atoms into one of value `signed(x)+signed(y)`,
   with a proof `signed x + signed y = signed z`.  Both operands go to `from_int`
   form (`signed_to_zform`), then `lit_add` folds them with `Stdlib.Z` computing
   `Z.+`; a net-negative result needs a closing `lit_neg` to land on the
   `— from_int` rendering of the combined atom. *)
let combine_lit env (xa, xs) (ya, ys) : (exp * int) * L.term =
  let xv = match xa with Nat n -> n | _ -> assert false in
  let yv = match ya with Nat n -> n | _ -> assert false in
  let v = xs * xv + ys * yv in
  let (zx, px) = signed_to_zform env xv xs in
  let (zy, py) = signed_to_zform env yv ys in
  let base =
    L.App (L.Name "eq_trans",
      [ L.App (L.Name "add_cong", [ px; py ]);
        L.App (L.Name "lit_add", [ zx; zy ]) ])
  in
  (* base : signed x + signed y = from_int (Z.+ zx zy), with Z.+ zx zy ≡ <v as ℤ>. *)
  if v >= 0 then ((Nat v, 1), base)              (* from_int (Z.+ …) ≡ from_int v *)
  else
    ((Nat (-v), -1),
     L.App (L.Name "eq_trans",
       [ base;
         L.App (L.Name "eq_sym",
           [ L.App (L.Name "lit_neg", [ z_dec (string_of_int (-v)) ]) ]) ]))
     (* from_int (Z.+ …) ≡ from_int (Z.— (-v)), then lit_neg back to — from_int (-v) *)

(* Fold the trailing run of foldable `Nat` literals of a SORTED atom list into a
   single literal (dropped if it nets to 𝟎), with a proof `lfold l = lfold
   folded`.  Sorted ⟹ the literals are a contiguous suffix; combine them two at a
   time from the right — each step an `add_assoc` to expose the rightmost pair and
   `add_congR`/[combine_lit] to fold it (`lit_add`, `Stdlib.Z` computing the sum). *)
let fold_lits env l : (exp * int) list * L.term =
  let is_lit (a, _) = is_foldable_lit a in
  let refl ll = L.App (L.Name "eq_refl", [ L.Exp (env, lfold_exp ll) ]) in
  let trans p q = L.App (L.Name "eq_trans", [ p; q ]) in
  (* combine the last two atoms of `front @ [x; y]` (both literals) into `z`,
     with a proof `lfold (front @ [x;y]) = lfold (front @ [z])`. *)
  let combine_step front x y =
    let (z, clit) = combine_lit env x y in
    match front with
    | [] -> (z, clit)
    | _ ->
      let lf = lfold_exp front in
      let assoc =
        L.App (L.Name "add_assoc",
          [ L.Exp (env, lf); L.Exp (env, signed_exp x); L.Exp (env, signed_exp y) ]) in
      let congr = L.App (L.Name "add_congR", [ L.Exp (env, lf); clit ]) in
      (z, trans assoc congr)
  in
  if List.length (List.filter is_lit l) <= 1 then (l, refl l)
  else
    let rec go l =
      match List.rev l with
      | y :: x :: front_rev ->
        let front = List.rev front_rev in
        let (z, step) = combine_step front x y in
        let l' = front @ [ z ] in
        if List.length (List.filter is_lit l') <= 1 then (l', step)
        else let (l'', rest) = go l' in (l'', trans step rest)
      | _ -> (l, refl l)
    in
    let (folded, pf) = go l in
    (* drop a net-𝟎 trailing literal: `lfold (syms @ [𝟎]) = lfold syms`. *)
    match List.rev folded with
    | (Nat 0, _) :: rest_rev ->
      let syms = List.rev rest_rev in
      let drop =
        match syms with
        | [] -> refl []                          (* lfold [𝟎] ≡ 𝟎 ≡ lfold [] *)
        | _ ->
          let lf = lfold_exp syms in
          L.App (L.Name "add_zero", [ L.Exp (env, lf); int_evidence env lf ])
      in
      (syms, trans pf drop)
    | _ -> (folded, pf)

(* Normalise [e] to its canonical signed-atom list — symbolic atoms sorted, the
   literal part cancelled (`n + —n`) then folded to one (or no) `from_int` — with
   a proof `e = lfold canon`.  Two `+`/`−` expressions are equal iff their
   canonical lists are; the literal fold matches PP's solver-side constant
   folding.  Each side: [normalize] (— to leaves) → sort by [atom_compare] (a
   permutation, [prove_eq_lnested]) → [reduce_cancel] → [fold_lits]. *)
let canonicalize env e : ((exp * int) list * L.term) option =
  let trans p q = L.App (L.Name "eq_trans", [ p; q ]) in
  match normalize env e with
  | None -> None
  | Some (l, p0) ->                                (* p0 : e = lfold l *)
    let sorted = List.sort atom_compare l in
    let p1 = prove_eq_lnested env l in             (* lfold l = lfold sorted *)
    let (rc, p2) = reduce_cancel env sorted in      (* lfold sorted = lfold rc *)
    let (fl, p3) = fold_lits env rc in              (* lfold rc = lfold fl *)
    Some (fl, trans p0 (trans p1 (trans p2 p3)))

(* `π (e1 = e2)` for two `+`/`−` expressions with the same canonical form — same
   symbolic atoms after cancellation and the same folded literal constant; None
   if either is unsupported or the canonical lists differ.  Bridges an
   arithmetic-reorder / normalisation gap (INS conjuncts, AR3_1) without `trust`. *)
let prove_sum_eq env e1 e2 : L.term option =
  match canonicalize env e1, canonicalize env e2 with
  | Some (f1, p1), Some (f2, p2) when f1 = f2 ->
    (* e1 = lfold f1 = lfold f2 = e2 *)
    Some (L.App (L.Name "eq_trans", [ p1; L.App (L.Name "eq_sym", [ p2 ]) ]))
  | _ -> None

(* `π (e = 𝟎)` when [e]'s signed atoms cancel/fold to nothing (e.g. `—a + a`,
   `3 − 2 − 1`).  [prove_sum_eq … (Nat 0)] can't — `𝟎` normalises to the *atom*
   `0`, not the empty list — so read the canonical form directly: empty ⟹ the
   proof `e = lfold [] ≡ 𝟎`. *)
let prove_sum_zero env e : L.term option =
  match canonicalize env e with
  | Some ([], p) -> Some p
  | _ -> None

(* `π (¬(from_int c ≤ 𝟎))` for a concrete positive literal c.  `from_int c ≤ 𝟎`
   reduces (le_elim, then the `to_int ∘ from_int` retract) to `Z.≤ c 0`, which
   `Stdlib.Z` decides `false` by head match on `Zpos … / Z0` for any magnitude —
   so `(…) ⊤ᵢ : ⊥`, O(1) (mirrors `one_not_leq_zero`, reused for c = 1). *)
let positive_lit env c : L.term =
  if c = 1 then L.Name "one_not_leq_zero"
  else
    L.Lambda ("_h", None,
      L.App (L.Name "le_elim",
        [ L.Exp (env, Nat c); L.Exp (env, Nat 0); L.Name "_h";
          L.Name "\xe2\x8a\xa4\xe1\xb5\xa2" (* ⊤ᵢ *) ]))

(* `π (e > 𝟎)` (= `π (¬(e ≤ 𝟎))`) when [e] canonicalises to a positive literal c
   (so symbolic cancellation like `x + 3 − x` still lands on 3, and a literal run
   folds via [fold_lits]).  Transport `¬(c ≤ 𝟎)` along the generated `e = c`.
   Used by AR2 (`a − b`) and AR4 (`E + F`); MAXINT-scale literals stay folded. *)
let prove_gt_zero env e : L.term option =
  match canonicalize env e with
  | Some ([ (Nat c, 1) ], eqpf) when c >= 1 ->     (* eqpf : e = lfold [Nat c] ≡ Nat c *)
    Some (L.App (L.Name "=\xe2\x87\x92",            (* =⇒ : π (A = B) → π A → π B *)
      [ L.App (L.Name "eq_sym",
          [ L.App (L.Name "not_cong",
              [ L.App (L.Name "leq_zero_eq", [ eqpf ]) ]) ]);
        positive_lit env c ]))
  | _ -> None

(* ---- ARITH: Farkas-style linear-combination contradiction ----

   PP's linear solver closes ⊥ from the `eᵢ ≤ 𝟎` hypotheses in scope without
   recording a certificate.  Reconstruct one: search small nonnegative
   multipliers λᵢ so that Σ λᵢ·eᵢ has every symbolic atom cancel and its literal
   part fold to a positive constant c — then emit

     positive_lit c (leq_subst_l (c = Σ…) (add_leq_zero … hᵢ …))

   i.e. `Σ ≤ 𝟎` substituted to `c ≤ 𝟎`, refuted by `c > 𝟎`.  The Σ-equality is
   generated by [prove_sum_eq] (which folds the literals via `Stdlib.Z`); no
   `trust`. *)
let arith_max_lambda = 8

let find_arith_contradiction env hyps =
  let vec atoms =
    List.fold_left (fun acc (a, s) ->
      let cur = try List.assoc a acc with Not_found -> 0 in
      (a, cur + s) :: List.remove_assoc a acc) [] atoms
  in
  let vecs = Array.of_list (List.map (fun (_, _, ats) -> vec ats) hyps) in
  let names = Array.of_list (List.map (fun (n, e, _) -> (n, e)) hyps) in
  let n_h = Array.length vecs in
  (* the combination's net vector must reduce to a positive constant: every
     non-literal atom cancels, and the constant is the signed sum of the
     foldable `Nat` literals' values (weighted by their net coefficients) *)
  let pos_const lambdas =
    let total = Hashtbl.create 8 in
    Array.iteri (fun j v ->
      if lambdas.(j) > 0 then
        List.iter (fun (a, c) ->
          let cur = try Hashtbl.find total a with Not_found -> 0 in
          Hashtbl.replace total a (cur + lambdas.(j) * c)) v) vecs;
    let ok = Hashtbl.fold (fun a c ok -> ok && (c = 0 || is_foldable_lit a))
               total true in
    let const = Hashtbl.fold (fun a c acc ->
                  match a with Nat v -> acc + c * v | _ -> acc) total 0 in
    if ok && const >= 1 then Some const else None
  in
  let lambdas = Array.make n_h 0 in
  let rec search i =
    if i = n_h then
      if Array.exists (fun l -> l > 0) lambdas
      then Option.map (fun c -> (Array.copy lambdas, c)) (pos_const lambdas)
      else None
    else
      let rec try_l l =
        if l > arith_max_lambda then None
        else begin
          lambdas.(i) <- l;
          match search (i + 1) with
          | Some r -> Some r
          | None -> try_l (l + 1)
        end
      in
      let r = try_l 0 in
      lambdas.(i) <- 0;
      r
  in
  if n_h = 0 then None
  else
    match search 0 with
    | None -> None
    | Some (ls, c) ->
      let uses =
        List.concat
          (List.init n_h (fun j ->
             List.init ls.(j) (fun _ -> names.(j))))
      in
      (match uses with
       | [] -> None
       | (n0, e0) :: rest ->
         let hsum, combined =
           List.fold_left (fun (pf, acc_e) (n, e) ->
             (L.App (L.Name "add_leq_zero",
                [ L.Exp (env, acc_e); L.Exp (env, e); pf; L.Name n ]),
              AOp (Add, acc_e, e)))
             (L.Name n0, e0) rest
         in
         Option.map
           (fun eqpf ->
              (* eqpf : Nat c = combined ; hsum : combined ≤ 𝟎.  leq_subst_l
                 substitutes to `c ≤ 𝟎`, refuted by positive_lit c. *)
              L.Refine (positive_lit env c,
                [ L.App (L.Name "leq_subst_l", [ eqpf; hsum ]) ]))
           (prove_sum_eq env (Nat c) combined))
