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

(* Whether a literal atom folds into a constant run.  Only `Nat` literals do:
   they fit OCaml's native `int`, so [prove_fold_lits] sums a contiguous run into
   one decimal that `Stdlib.Z` then *computes* — no `lit_add` apparatus, that
   legacy machinery existed only because the pre-Z encoding couldn't compute.  A
   `BigNat` (apero's 2⁶⁴ bounds) is left an opaque atom — compared structurally,
   never summed — so it is false here and [atom_compare] keeps it among the
   symbolic atoms. *)
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

(* ====================================================================
   to_int-transport: prove an arithmetic equality by reflecting it onto
   `to_int e` (Stdlib.Z), where the literal arithmetic *computes* and the
   `0 + z` / `z + 0` identities are reductions.  Only reorder-swaps and
   cancellations cost a lemma; constant folding is `Stdlib.Z` reducing a
   ground sum, so the old `lit_add` / signed-literal apparatus is gone.
   ==================================================================== *)

(* ---- Z (Stdlib.Z) term builders.  The emitted file is ℤ-global, so bare
   `+` / `—` / decimals are `Stdlib.Z`'s; a τ ι atom reflects via `to_int`. *)
let z_neg (t : L.term) : L.term = L.App (L.Name "\xe2\x80\x94", [ t ])     (* — t *)
let z_add (a : L.term) (b : L.term) : L.term = L.Infix ("+", a, b)
let z_toint env (a : exp) : L.term = L.App (L.Name "to_int", [ L.Exp (env, a) ])

(* Eq combinators that elide reflexive steps.  An already-canonical sub-sum
   yields `eq_refl`, so a near-sorted expression's swap/cancel/fold chain
   collapses instead of nesting trivial `eq_trans (eq_refl …) …` — the common
   case (PP usually records arithmetic already normalised) becomes one step. *)
let refl t = L.App (L.Name "eq_refl", [ t ])
let as_refl = function L.App (L.Name "eq_refl", [ a ]) -> Some a | _ -> None
let trans p q =
  match as_refl p, as_refl q with Some _, _ -> q | _, Some _ -> p
  | _ -> L.App (L.Name "eq_trans", [ p; q ])
let sym p = match as_refl p with Some _ -> p | None -> L.App (L.Name "eq_sym", [ p ])

(* ℤ congruences, likewise refl-eliding (a reflexive operand recovers the fixed
   term from its `eq_refl`, collapsing the congruence to a reflexivity). *)
let z_congL b p = match as_refl p with
  | Some a -> refl (z_add a b) | None -> L.App (L.Name "Z_congL", [ b; p ])
let z_congR a p = match as_refl p with
  | Some b -> refl (z_add a b) | None -> L.App (L.Name "Z_congR", [ a; p ])
let z_neg_cong p = match as_refl p with
  | Some a -> refl (z_neg a) | None -> L.App (L.Name "Z_neg_cong", [ p ])
let z_cong px py = match as_refl px, as_refl py with
  | Some a, Some b -> refl (z_add a b)
  | Some a, None -> z_congR a py
  | None, Some b -> z_congL b px
  | None, None -> L.App (L.Name "Z_cong", [ px; py ])

(* A signed atom as a ℤ term.  A foldable `Nat` literal is its bare decimal
   (`to_int (from_int n)` reduces to it), so a run of them folds by computation;
   any other atom is `to_int a`.  A negative sign wraps in `—`. *)
let zatom_base env (a : exp) : L.term =
  match a with Nat n -> z_dec (string_of_int n) | _ -> z_toint env a
let zatom env (a, s) : L.term =
  let b = zatom_base env a in if s >= 0 then b else z_neg b

(* Left-nested ℤ sum of a signed-atom list; `[]` is `0` (Stdlib.Z's identity). *)
let zfold env (l : (exp * int) list) : L.term =
  match l with
  | [] -> z_dec "0"
  | s0 :: rest -> List.fold_left (fun acc s -> z_add acc (zatom env s)) (zatom env s0) rest

(* π (zfold la + zfold lb = zfold (la @ lb)): peel lb's tail, reassociating each
   element onto la (`+_assoc`).  An empty side is the identity *by reduction*
   (`0 + z ↪ z`, `z + 0 ↪ z`), so those close with `eq_refl`. *)
let rec z_concat env la lb : L.term =
  match la, List.rev lb with
  | _, [] -> refl (zfold env la)
  | [], _ -> refl (zfold env lb)
  | _, [ _ ] -> refl (z_add (zfold env la) (zfold env lb))
  | _, last :: front_rev ->
    let front = List.rev front_rev in
    trans (sym (L.App (L.Name "+_assoc",
                  [ zfold env la; zfold env front; zatom env last ])))
          (z_congL (zatom env last) (z_concat env la front))

(* π (— zatom s = zatom (negate s)): `— —` collapses by `—_idem` (a negative
   atom), else reflexive (negating a positive atom just adds the `—`). *)
let z_neg_atom env (a, s) : L.term =
  let b = zatom_base env a in
  if s >= 0 then refl (z_neg b)
  else L.App (L.Name "\xe2\x80\x94_idem", [ b ])    (* — — b = b *)

(* π (— zfold l = zfold (negate l)): distribute `—` over the left-nested sum
   (`distr_—_+`), recursing into the prefix. *)
let rec z_neg_distr env l : L.term =
  match l with
  | [] -> refl (z_dec "0")                          (* — 0 ≡ 0 *)
  | [ s ] -> z_neg_atom env s
  | _ ->
    let n = List.length l in
    let last = List.nth l (n - 1) in
    let front = List.filteri (fun i _ -> i < n - 1) l in
    trans (L.App (L.Name "distr_\xe2\x80\x94_+", [ zfold env front; zatom env last ]))
          (z_cong (z_neg_distr env front) (z_neg_atom env last))

(* Given `pa : to_int e = zfold la`, build `(negate la, to_int (neg e) = zfold
   (negate la))`.  `to_int (neg e) ↪ — to_int e` (B.lp rule) places the `—`, so
   rewrite under it with `pa` (`Z_neg_cong`) then distribute (`z_neg_distr`).
   Handles `Neg` of any sub-expression. *)
let neg_push env (la, pa) : (exp * int) list * L.term =
  let lneg = List.map (fun (a, s) -> (a, -s)) la in
  let p = trans (z_neg_cong pa) (z_neg_distr env la) in
  (lneg, p)

(* Reflect [e] onto its flattened ℤ signed-atom list with a proof
   `to_int e = zfold atoms`.  `to_int` pushes through `plus`/`neg` by REDUCTION
   (the B.lp rules; `minus` desugars), so the proof carries no push step — just
   the `Z_cong` / `z_concat` reassembly — mirroring the data-only [flatten_signed]. *)
let rec toint_flat env e : ((exp * int) list * L.term) option =
  match e with
  | Nat 0 -> Some ([], refl (z_dec "0"))            (* to_int 𝟎 ≡ 0 = zfold [] *)
  | _ when is_atom_exp e -> Some ([ (e, 1) ], refl (zatom env (e, 1)))
  | Neg a ->
    (match toint_flat env a with
     | Some (la, pa) -> Some (neg_push env (la, pa))
     | None -> None)
  | AOp (Add, x, y) -> combine_add env x y
  | AOp (Sub, x, y) -> toint_flat env (AOp (Add, x, Neg y))
  | _ -> None
and combine_add env x y : ((exp * int) list * L.term) option =
  match toint_flat env x, toint_flat env y with
  | Some (lx, px), Some (ly, py) ->
    (* to_int (plus x y) ↪ to_int x + to_int y  (B.lp rule)
                         = zfold lx + zfold ly  [Z_cong]
                         = zfold (lx @ ly)       [z_concat] *)
    let p = trans (z_cong px py) (z_concat env lx ly) in
    Some (lx @ ly, p)
  | _ -> None

(* π (zfold l = zfold l') where l' swaps the adjacent atoms at (k, k+1): a single
   `+_com` (the pair is the whole sum) or `assoc · congR comm · assoc⁻¹` under the
   left-nested prefix, then `Z_congL` back over the suffix. *)
let prove_swap env l k : L.term =
  let nth i = List.nth l i in
  let pre = List.filteri (fun i _ -> i < k) l in
  let suf = List.filteri (fun i _ -> i > k + 1) l in
  let a = zatom env (nth k) and b = zatom env (nth (k + 1)) in
  let core =
    match pre with
    | [] -> L.App (L.Name "+_com", [ a; b ])
    | _ ->
      let p = zfold env pre in
      trans (L.App (L.Name "+_assoc", [ p; a; b ]))
        (trans (z_congR p (L.App (L.Name "+_com", [ a; b ])))
           (sym (L.App (L.Name "+_assoc", [ p; b; a ]))))
  in
  List.fold_left (fun acc s -> z_congL (zatom env s) acc) core suf

let swap_list l k =
  List.mapi (fun i x -> if i = k then List.nth l (k + 1)
                        else if i = k + 1 then List.nth l k else x) l

let first_inversion l =
  let rec go i = function
    | x :: (y :: _ as tl) -> if atom_compare x y > 0 then Some i else go (i + 1) tl
    | _ -> None
  in go 0 l

(* π (zfold l = zfold (sort l)): bubble-sort, each adjacent inversion a swap. *)
let rec prove_sort env l : L.term =
  match first_inversion l with
  | None -> refl (zfold env l)
  | Some k -> trans (prove_swap env l k) (prove_sort env (swap_list l k))

(* π (zfold l = zfold l') cancelling the adjacent pair `(a,−1),(a,+1)` at (k,k+1).
   With a prefix it is `simpl_inv_right` (`(p + —a) + a = p`); with none, the pair
   is `Z_neg_add` and the trailing `0 +` collapses by reduction. *)
let prove_cancel env l k : L.term =
  let a = fst (List.nth l k) in
  let pre = List.filteri (fun i _ -> i < k) l in
  let suf = List.filteri (fun i _ -> i > k + 1) l in
  let neg_a_a = L.App (L.Name "Z_neg_add", [ zatom_base env a ]) in   (* — a + a = 0 *)
  let fold_congL =
    List.fold_left (fun acc s -> z_congL (zatom env s) acc) in
  match pre with
  | _ :: _ ->
    let core = L.App (L.Name "simpl_inv_right", [ zfold env pre; zatom_base env a ]) in
    fold_congL core suf
  | [] ->
    (match suf with
     | [] -> neg_a_a
     | s0 :: rest ->
       fold_congL (z_congL (zatom env s0) neg_a_a) rest)

let rec reduce_cancel env l : (exp * int) list * L.term =
  let rec find i = function
    | (x, sx) :: ((y, sy) :: _ as tl) ->
      if x = y && sx + sy = 0 then Some i else find (i + 1) tl
    | _ -> None
  in
  match find 0 l with
  | None -> (l, refl (zfold env l))
  | Some k ->
    let l' = List.filteri (fun i _ -> i <> k && i <> k + 1) l in
    let p_step = prove_cancel env l k in
    let r, p_rest = reduce_cancel env l' in
    (r, trans p_step p_rest)

(* Fold the trailing run of foldable `Nat` literals into one (or none) — sorted ⟹
   they are a contiguous suffix.  `Stdlib.Z` *computes* each combined sum, so the
   step is `+_assoc` to expose the rightmost pair then `eq_refl` (no `lit_add`);
   a net-zero trailing literal drops by the `z + 0` reduction. *)
let prove_fold_lits env l : (exp * int) list * L.term =
  let is_lit (a, _) = is_foldable_lit a in
  if List.length (List.filter is_lit l) <= 1 then (l, refl (zfold env l))
  else
    let combine_step front x y =
      let uv, su = (match x with (Nat u, s) -> (u, s) | _ -> assert false) in
      let vv, sv = (match y with (Nat v, s) -> (v, s) | _ -> assert false) in
      let w = (su * uv) + (sv * vv) in
      let z = if w >= 0 then (Nat w, 1) else (Nat (-w), -1) in
      let step =
        match front with
        | [] -> refl (zatom env z)              (* zatom x + zatom y ≡ zatom z *)
        | _ ->
          let lf = zfold env front in
          trans (L.App (L.Name "+_assoc", [ lf; zatom env x; zatom env y ]))
                (z_congR lf (refl (zatom env z)))
      in (z, step)
    in
    let rec go l =
      match List.rev l with
      | y :: x :: front_rev when is_lit x && is_lit y ->
        let front = List.rev front_rev in
        let z, step = combine_step front x y in
        let l' = front @ [ z ] in
        if List.length (List.filter is_lit l') <= 1 then (l', step)
        else let l'', rest = go l' in (l'', trans step rest)
      | _ -> (l, refl (zfold env l))
    in
    let folded, pf = go l in
    match List.rev folded with
    | (Nat 0, _) :: rest_rev -> (List.rev rest_rev, pf)   (* zfold (syms@[𝟎]) ≡ zfold syms *)
    | _ -> (folded, pf)

(* Reflect [e] onto its canonical signed-atom list with a proof
   `to_int e = zfold canon`: flatten ([toint_flat]) → sort → cancel → fold the
   literal run.  Two expressions are equal iff their canon lists match; the
   constant fold is `Stdlib.Z` computing, matching PP's solver-side folding. *)
let canonicalize env e : ((exp * int) list * L.term) option =
  match toint_flat env e with
  | None -> None
  | Some (l, p0) ->                                 (* p0 : to_int e = zfold l *)
    let sorted = List.sort atom_compare l in
    let p1 = prove_sort env l in                    (* zfold l = zfold sorted *)
    let rc, p2 = reduce_cancel env sorted in        (* zfold sorted = zfold rc *)
    let fl, p3 = prove_fold_lits env rc in          (* zfold rc = zfold fl *)
    Some (fl, trans p0 (trans p1 (trans p2 p3)))

(* ====================================================================
   Cancel recipe: the *tactic* form of the to_int-transport, for closing
   `to_int e = c` where [e]'s atoms cancel/fold to the single literal c.
   Where [canonicalize] builds a congruence *term*, this emits the same
   bubble-sort + cancellation as *pattern-free* `rewrite`s on the post-`simplify`
   goal: `simplify` computes `to_int`, the negation/associativity prefix left-nests
   it, then each sort swap is `rewrite +_com` (the innermost, leftmost pair) or
   `rewrite Z_swap2` (the outermost pair), and the single inverse pair cancels with
   `rewrite Z_neg_add`; reflexivity computes the trailing literal run to c.

   Pattern-free on purpose: a `rewrite .[<rendered subterm>]` would have to predict
   `simplify`'s exact output, and a non-matching SSReflect pattern crashes the
   lambdapi matcher.  The cost is reach: only swaps at the first (k=0) or last
   (k=len−2) position are realisable without a target, and a single symbolic inverse
   pair keeps the no-target cancel unambiguous — so this handles the dominant AR4 /
   sum-zero shapes (one inverse pair + a literal, ≤3 atoms) and *bails to the
   explicit term* ([None]) otherwise.  No correctness risk: a bail keeps the proven
   congruence term. *)
let cancel_recipe _env e : (L.t * int) option =
  let rw ?(rep = false) ?(rtl = false) name =
    L.Rewrite { try_ = false; repeat_ = rep; rtl; pat = None; name } in
  let is_lit (a, _) = is_foldable_lit a in
  match flatten_signed e with
  | None -> None
  | Some l ->
    let lits = List.filter is_lit l and syms = List.filter (fun a -> not (is_lit a)) l in
    let c = List.fold_left
        (fun acc (a, s) -> match a with Nat n -> acc + (s * n) | _ -> acc) 0 lits in
    (* Pick the no-argument cancel lemma for this shape — `rewrite <lemma>` infers
       the atoms from the goal, so it works on `prj k _x` atoms (rendering them into
       a target crashes the lambdapi matcher).  Reach: one inverse pair plus at most
       one literal (≤3 atoms, the AR3-followup shapes that dominate AR4); the pair's
       position in the left-nested sum (front / end / split-by-the-literal) and the
       sign of its first-listed atom select the lemma.  Anything else → [None] (the
       caller keeps the proven congruence term).  [Some None] = no symbolic pair, so
       the literal run just computes under `reflexivity`. *)
    let step_name : string option option =
      let first_sym_neg = match syms with (_, s) :: _ -> s < 0 | [] -> false in
      let litpos =                                   (* index of the lone literal, if any *)
        let rec go i = function
          | a :: tl -> if is_lit a then Some i else go (i + 1) tl
          | [] -> None
        in go 0 l in
      match syms with
      | [] when lits <> [] -> Some None
      | [ (x1, s1); (x2, s2) ] when x1 = x2 && s1 + s2 = 0 && List.length lits <= 1 ->
        (match litpos with
         | None | Some 2 ->                           (* pair at the front: `(±x + ∓x) + …` *)
           Some (Some (if first_sym_neg then "Z_neg_add" else "-_same"))
         | Some 0 ->                                  (* pair at the end: `(l + ±x) + ∓x` *)
           Some (Some (if first_sym_neg then "Z_sub_add" else "Z_add_sub"))
         | Some 1 ->                                  (* pair split by the literal: `(±x + l) + ∓x` *)
           Some (Some (if first_sym_neg then "Zc_nlx" else "Zc_xln"))
         | _ -> None)
      | _ -> None
    in
    (match step_name with
     | None -> None
     | Some step ->
       let prefix =
         [ L.Simplify; rw ~rep:true "distr_\xe2\x80\x94_+";
           rw ~rep:true "\xe2\x80\x94_idem"; rw ~rep:true ~rtl:true "+_assoc" ] in
       let cancel = match step with None -> [] | Some nm -> [ rw nm ] in
       let rec seq = function
         | [] -> L.Step L.Reflexivity
         | [ t ] -> L.Step t
         | t :: r -> L.Then (t, seq r) in
       Some (seq (prefix @ cancel @ [ L.Reflexivity ]), c))

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

(* Bridge a τ ι equality from its reflected ℤ proof: `e = from_int (to_int e)`
   (`int_retract`) then `feq from_int` of `zpf : to_int e = …`. *)
let from_toint env e zpf : L.term =
  trans (L.App (L.Name "int_retract", [ L.Exp (env, e); int_evidence env e ]))
        (L.App (L.Name "feq", [ L.Name "from_int"; zpf ]))

(* `π (e1 = e2)` for two `+`/`−` expressions denoting the same signed-atom
   multiset after cancellation; None if either is unsupported or the canon lists
   differ.  `to_int e1 = zfold = to_int e2`, lifted to τ ι by the [toint_eq]
   reflection lemma (one node — no inlined int_retract/feq/eq_sym scaffolding).
   Common no-reorder case (e.g. AR3's `𝟏−a = 𝟏−a`): the sides are already
   identical, so the proof is `eq_refl` — no canonicalisation or `to_int` bridge.
   (The commutation-free majority is emitted as a `simplify`-based recipe `have`
   upstream by [Emit_ctx.arith_eq_have]; this term path is the reorder/cancel
   remainder where atoms genuinely permute.) *)
let prove_sum_eq env e1 e2 : L.term option =
  if e1 = e2 then Some (refl (L.Exp (env, e1)))
  else
    match canonicalize env e1, canonicalize env e2 with
    | Some (f1, p1), Some (f2, p2) when f1 = f2 ->
      let zeq = trans p1 (sym p2) in                (* to_int e1 = to_int e2 *)
      Some (L.App (L.Name "toint_eq",
              [ L.Exp (env, e1); L.Exp (env, e2);
                int_evidence env e1; int_evidence env e2; zeq ]))
    | _ -> None

(* `π (e = 𝟎)` when [e]'s atoms cancel to the empty multiset: `to_int e = 0`,
   lifted by `from_int` (`from_int 0 ≡ 𝟎`). *)
let prove_sum_zero env e : L.term option =
  match canonicalize env e with
  | Some ([], p) -> Some (from_toint env e p)
  | _ -> None

(* `π (e > 𝟎)` when [e] cancels/folds to a positive literal c: transport
   `¬(from_int c ≤ 𝟎)` (`positive_lit`) along the generated `e = from_int c`. *)
let prove_gt_zero env e : L.term option =
  match canonicalize env e with
  | Some ([ (Nat c, 1) ], p) when c >= 1 ->         (* p : to_int e = c *)
    let e_eq_c = from_toint env e p in              (* e = from_int c *)
    Some (L.App (L.Name "=\xe2\x87\x92",            (* =⇒ : π (A = B) → π A → π B *)
      [ sym (L.App (L.Name "not_cong",
              [ L.App (L.Name "leq_zero_eq", [ e_eq_c ]) ]));
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
