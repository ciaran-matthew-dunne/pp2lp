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
  | Var _ | Lit _ | App _ | EApp _ | SetOp _ | SetImage _ | Inter _
  | Union _ | Range _ | Maplet _ | Inverse _ | SetLit _ | DomRestrict _
  | RanRestrict _ | BoolOf _ | Compr _ -> true
  | AOp _ | Neg _ -> false

(* The native-int value of a literal that folds into the reified constant: a
   `Lit` small enough to fit OCaml's `int`, so [lin_normal] sums it into the
   constant and [reify] emits an `Llit`.  A too-big `Lit` (apero's 2⁶⁴ bounds)
   overflows, so it stays a symbolic atom — reified as a `Lvar`, compared by
   index, never summed — hence None here (apero's 2⁶⁴ bounds). *)
let fold_val = function Lit s -> int_of_string_opt s | _ -> None

(* `prod(k, a)` / `prod(a, k)` with a *foldable* literal coefficient: its decimal
   string and the scaled operand.  Two arms (not one `|`-pattern) so each operand
   position is guarded independently; a too-big coefficient leaves the whole
   `prod` a symbolic atom. *)
let prod_coeff = function
  | SetOp ("prod", [ Lit ks; a ]) when int_of_string_opt ks <> None -> Some (ks, a)
  | SetOp ("prod", [ a; Lit ks ]) when int_of_string_opt ks <> None -> Some (ks, a)
  | _ -> None

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
  | Lit "0" | Neg (Lit "0") -> L.Name "zero_in_int"
  | Lit s -> L.App (L.Name "from_int_in_int", [z_dec s])
  | Neg a -> L.App (L.Name "neg_in_int", [ex a])
  | AOp (Add, x, y) -> L.App (L.Name "add_in_int", [ex x; ex y])
  | AOp (Sub, x, y) -> L.App (L.Name "add_in_int", [ex x; ex (Neg y)])
  (* literal-coefficient product `n*x` (rendered `mult`): integer-valued by mult_def. *)
  | SetOp ("prod", [ (Lit _ as k); x ]) | SetOp ("prod", [ x; (Lit _ as k) ]) ->
    L.App (L.Name "mult_in_int", [ex k; ex x])
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
  | Lit "0" -> Some []
  (* `prod(k, e)` / `prod(e, k)` with a foldable literal coefficient k is arithmetic
     scaling k·e (a literal can't be a Cartesian operand): scale e's atom coefficients
     by k.  Before the `is_atom_exp` catch — a `prod` is a SetOp, hence an atom
     otherwise; a too-big coefficient ([prod_coeff] = None) takes that atom path. *)
  | _ when prod_coeff e <> None ->
    let (ks, a) = Option.get (prod_coeff e) in
    let k = int_of_string ks in
    Option.map (List.map (fun (x, s) -> (x, k * s))) (flatten_signed a)
  | AOp (Add, a, b) -> app (flatten_signed a) (flatten_signed b)
  | AOp (Sub, a, b) -> app (flatten_signed a) (negate (flatten_signed b))
  | Neg a -> negate (flatten_signed a)        (* — over any sub-expr (incl. scaled prod) *)
  | _ when is_atom_exp e -> Some [ (e, 1) ]
  | _ -> None

let signed_exp (a, s) = if s >= 0 then a else Neg a

(* Left-nested sum of a (non-empty) signed-atom list, as a PP expression. *)
let lfold_exp = function
  | [] -> Lit "0"
  | s0 :: rest ->
    List.fold_left (fun acc s -> AOp (Add, acc, signed_exp s)) (signed_exp s0) rest

(* ====================================================================
   Reflective ℤ-linear equality: prove `e1 = e2` (τ ι) by reflecting onto
   `to_int` (Stdlib.Z) via [toint_eq] and discharging the residual ℤ goal with
   the [reflect] lemma (lemmas/Reflect.lp) — reify each side to an `LE` over an
   environment ρ of the distinct atoms, COMPUTE a canonical normal form, close by
   `eq_refl`.  No reorder/cancel rewrite chain, no subterm targeting (which
   crashes on `prj k _x` atoms); the per-site proof is one
   `toint_eq … (reflect ρ r1 r2 (eq_refl _))` term that also sits under binders.
   ==================================================================== *)

(* Net signed-atom multiset + integer constant of a linear expr: `Nat` literals
   fold into the constant, every other atom (incl a too-big literal) stays symbolic and is
   compared structurally.  Two exprs denote the same value iff their [lin_normal]s
   are equal.  None if [e] is not `+`/`−`-linear. *)
let lin_normal e : ((exp * int) list * int) option =
  match flatten_signed e with
  | None -> None
  | Some atoms ->
    let const =
      List.fold_left
        (fun c (a, s) -> match fold_val a with Some n -> c + (s * n) | None -> c)
        0 atoms in
    let net =
      List.fold_left (fun acc (a, s) ->
        match fold_val a with
        | Some _ -> acc
        | None ->
          let cur = try List.assoc a acc with Not_found -> 0 in
          (a, cur + s) :: List.remove_assoc a acc)
        [] atoms in
    let net = List.filter (fun (_, s) -> s <> 0) net in
    Some (List.sort (fun (a, _) (b, _) -> compare a b) net, const)

(* The distinct symbolic atoms of [es] (the `Lvar` leaves [reify] emits), in
   first-occurrence order.  ρ is built from these, so a reified `Lvar i` resolves
   to `to_int (atom i)`. *)
let collect_atoms es : exp list =
  let rec go acc e =
    match e with
    | AOp ((Add | Sub), a, b) -> go (go acc a) b
    | Neg a -> go acc a
    | _ when prod_coeff e <> None -> go acc (snd (Option.get (prod_coeff e)))
    | _ when fold_val e <> None -> acc        (* foldable literal: folds, not an atom *)
    | _ when is_atom_exp e -> if List.mem e acc then acc else acc @ [ e ]
    | _ -> acc
  in
  List.fold_left go [] es

(* Reify a linear expr to an `LE` term, mirroring its `+`/`−`/`neg` structure so
   `den ρ (reify e) ≡ to_int e` by reduction.  a foldable literal → `Llit`; any other atom →
   `Lvar <its index>`. *)
let rec reify idx e : L.term =
  match e with
  | AOp (Add, a, b) -> L.App (L.Name "Ladd", [ reify idx a; reify idx b ])
  | AOp (Sub, a, b) ->
    L.App (L.Name "Ladd", [ reify idx a; L.App (L.Name "Lneg", [ reify idx b ]) ])
  | Neg a -> L.App (L.Name "Lneg", [ reify idx a ])
  | _ when prod_coeff e <> None ->
    let (ks, a) = Option.get (prod_coeff e) in
    L.App (L.Name "Lmul", [ z_dec ks; reify idx a ])
  | Lit n when int_of_string_opt n <> None -> L.App (L.Name "Llit", [ z_dec n ])
  | _ when is_atom_exp e ->
    L.App (L.Name "Lvar", [ L.Name (string_of_int (idx e)) ])
  | _ -> failwith "reflect_eq: non-linear expression"

(* `π (e1 = e2)` for two linear exprs with equal value: reflect onto ℤ.  ρ holds
   `to_int <atom>` for each distinct atom of e1, e2; [reflect] checks the reified
   sides COMPUTE to the same canonical normal form (discharged by `eq_refl`).
   None when they are not equal linear combinations (callers fall through). *)
let reflect_eq env e1 e2 : L.term option =
  match lin_normal e1, lin_normal e2 with
  | Some n1, Some n2 when n1 = n2 ->
    let atoms = collect_atoms [ e1; e2 ] in
    let idx a =
      let rec pos i = function
        | x :: _ when x = a -> i
        | _ :: tl -> pos (i + 1) tl
        | [] -> failwith "reflect_eq: atom index"
      in pos 0 atoms in
    let rho =
      List.fold_right
        (fun a rest ->
           L.Infix ("\xe2\xb8\xac",                          (* ⸬ *)
             L.App (L.Name "to_int", [ L.Exp (env, a) ]), rest))
        atoms (L.Name "\xe2\x96\xa1")                        (* □ *) in
    Some (L.App (L.Name "toint_eq",
      [ L.Exp (env, e1); L.Exp (env, e2);
        int_evidence env e1; int_evidence env e2;
        L.App (L.Name "reflect",
          [ rho; reify idx e1; reify idx e2;
            L.App (L.Name "eq_refl", [ L.Hole ]) ]) ]))
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
        [ L.Exp (env, Lit (string_of_int c)); L.Exp (env, Lit "0"); L.Name "_h";
          L.Name "\xe2\x8a\xa4\xe1\xb5\xa2" (* ⊤ᵢ *) ]))

(* `π (e1 = e2)` for two `+`/`−` exprs denoting the same value: the `e1 = e2`
   fast path is `eq_refl`, otherwise reflect onto ℤ ([reflect_eq]).  None if
   either is non-linear or they are not equal. *)
let prove_sum_eq env e1 e2 : L.term option =
  if e1 = e2 then Some (L.App (L.Name "eq_refl", [ L.Exp (env, e1) ]))
  else reflect_eq env e1 e2

(* `π (p = q)` for two predicates differing only by arithmetic normalisation of
   their leaf expressions — AR10's solver step `solveur(p) = q` (e.g. `¬(-(-x) = x)`
   ↦ `¬(x = x)`).  Recurse through the `¬`/`=`/`≤` shapes PP's arithmetic
   simplifier produces, composing one congruence lemma per connective and closing
   each `=`/`≤` leaf with [prove_sum_eq].  None for any other shape or a
   non-linear leaf, so the caller can fall back to the plain no-op skip. *)
let rec prove_pred_eq env p q : L.term option =
  let ( let* ) = Option.bind in
  match p, q with
  | Unary (Not, p'), Unary (Not, q') ->
    let* h = prove_pred_eq env p' q' in
    Some (L.App (L.Name "not_cong", [ h ]))
  | Eq (a, c), Eq (b, d) ->
    let* h1 = prove_sum_eq env a b in
    let* h2 = prove_sum_eq env c d in
    Some (L.App (L.Name "eq_cong", [ h1; h2 ]))
  | Leq (a, c), Leq (b, d) ->
    let* h1 = prove_sum_eq env a b in
    let* h2 = prove_sum_eq env c d in
    Some (L.App (L.Name "leq_cong", [ h1; h2 ]))
  | _ -> None

(* `π (e = 𝟎)` when [e]'s atoms cancel to nothing: reflect against the literal 0
   (`Exp (Lit "0") ≡ 𝟎`). *)
let prove_sum_zero env e : L.term option = reflect_eq env e (Lit "0")

(* `π (e > 𝟎)` when [e] cancels/folds to a positive literal c: transport
   `¬(from_int c ≤ 𝟎)` (`positive_lit`) along the reflected `e = from_int c`. *)
let prove_gt_zero env e : L.term option =
  match lin_normal e with
  | Some ([], c) when c >= 1 ->
    (match reflect_eq env e (Lit (string_of_int c)) with
     | Some e_eq_c ->                                  (* e_eq_c : e = from_int c *)
       Some (L.App (L.Name "=\xe2\x87\x92",            (* =⇒ : π (A = B) → π A → π B *)
         [ L.App (L.Name "eq_sym",
             [ L.App (L.Name "not_cong",
                 [ L.App (L.Name "leq_zero_eq", [ e_eq_c ]) ]) ]);
           positive_lit env c ]))
     | None -> None)
  | _ -> None

(* ---- ARITH: Fourier–Motzkin refutation with a Farkas certificate ----

   PP's linear solver closes ⊥ from the `eᵢ ≤ 𝟎` hypotheses in scope without
   recording how.  Reconstruct the certificate by Fourier–Motzkin elimination:
   carry on every derived constraint the *nonnegative integer combination* of the
   original hypotheses that produced it.  Eliminating the variable atoms one by
   one, an infeasible system collapses to `c ≤ 𝟎` with a positive constant c, and
   that constraint's recorded combination Σ λᵢ·eᵢ = c is the witness.  Emit

     positive_lit c (leq_subst_l (c = Σ…) (add_leq_zero … hᵢ …))

   i.e. `Σ ≤ 𝟎` substituted to `c ≤ 𝟎`, refuted by `c > 𝟎`; the Σ-equality comes
   from [prove_sum_eq] (folds the literals via `Stdlib.Z`), no `trust`.  Complete
   for ℚ-linear refutation, so telescoping ≤/< chains, sum-positivity and weighted
   sums (distinct literal coefficients) all fall out of one elimination — no
   multiplier enumeration, no length cap.  A genuinely non-linear goal (a product
   of two variables, e.g. `x·z ≤ y·z`) leaves an atom that never cancels, so the
   search correctly returns None. *)
let rec gcd a b = if b = 0 then abs a else gcd b (a mod b)

(* A Fourier–Motzkin constraint `Σ vars[a]·a + cst ≤ 𝟎`, equal by construction to
   `Σ org[i]·eᵢ` over the original hypotheses with every org[i] ≥ 0.  [vars] holds
   only non-foldable atoms — foldable literals fold into [cst] — and never a zero
   coefficient. *)
type fm_con = { vars : (exp * int) list; cst : int; org : int array }

let find_arith_contradiction env hyps =
  let n_h = List.length hyps in
  let names = Array.of_list (List.map (fun (n, e, _) -> (n, e)) hyps) in
  (* fold a signed-atom list into (non-foldable atoms, folded constant) *)
  let split_atoms atoms =
    let tbl = Hashtbl.create 8 in
    List.iter (fun (a, s) ->
      Hashtbl.replace tbl a ((try Hashtbl.find tbl a with Not_found -> 0) + s)) atoms;
    Hashtbl.fold (fun a c (vars, cst) ->
      if c = 0 then (vars, cst)
      else match fold_val a with
        | Some v -> (vars, cst + c * v)
        | None -> ((a, c) :: vars, cst)) tbl ([], 0)
  in
  (* k1·v1 + k2·v2 over atom lists, zero coefficients dropped *)
  let lin_comb k1 v1 k2 v2 =
    let tbl = Hashtbl.create 8 in
    let add k = List.iter (fun (a, c) ->
      Hashtbl.replace tbl a ((try Hashtbl.find tbl a with Not_found -> 0) + k * c)) in
    add k1 v1; add k2 v2;
    Hashtbl.fold (fun a c acc -> if c = 0 then acc else (a, c) :: acc) tbl []
  in
  (* Build the refutation term from a multiplier vector [ls] whose weighted sum
     folds to the positive constant [c]: `Σ ≤ 𝟎` substituted to `c ≤ 𝟎`, refuted
     by `c > 𝟎`.  The Σ-equality `from_int c = combined` is generated by
     [prove_sum_eq] (which folds the literals via `Stdlib.Z`); no `trust`. *)
  let build_cert ls c =
    let uses =
      List.concat
        (List.init n_h (fun j ->
           List.init ls.(j) (fun _ -> names.(j))))
    in
    match uses with
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
           (* eqpf : from_int c = combined ; hsum : combined ≤ 𝟎.  leq_subst_l
              substitutes to `c ≤ 𝟎`, refuted by positive_lit c. *)
           L.Refine (positive_lit env c,
             [ L.App (L.Name "leq_subst_l", [ eqpf; hsum ]) ]))
        (prove_sum_eq env (Lit (string_of_int c)) combined)
  in
  if n_h = 0 then None
  else begin
    let cons0 =
      List.mapi (fun i (_, _, atoms) ->
        let (vars, cst) = split_atoms atoms in
        { vars; cst; org = Array.init n_h (fun j -> if j = i then 1 else 0) })
        hyps
    in
    (* divide a constraint through by the gcd of all its coefficients — smaller
       integers, identical meaning and (scaled) certificate *)
    let reduce c =
      let g = List.fold_left (fun g (_, k) -> gcd g k) c.cst c.vars in
      let g = Array.fold_left gcd g c.org in
      let g = if g = 0 then 1 else g in
      if g = 1 then c
      else { vars = List.map (fun (a, k) -> (a, k / g)) c.vars;
             cst = c.cst / g; org = Array.map (fun k -> k / g) c.org }
    in
    let cv v c = match List.assoc_opt v c.vars with Some k -> k | None -> 0 in
    (* eliminate the atom that forks the fewest new constraints (|pos|·|neg|) *)
    let pick_atom cons =
      let atoms =
        List.sort_uniq compare (List.concat_map (fun c -> List.map fst c.vars) cons) in
      let scored = List.map (fun v ->
        let p = List.length (List.filter (fun c -> cv v c > 0) cons) in
        let n = List.length (List.filter (fun c -> cv v c < 0) cons) in
        (p * n, v)) atoms in
      match List.sort (fun (a, _) (b, _) -> compare a b) scored with
      | (_, v) :: _ -> Some v
      | [] -> None
    in
    (* guards: bail (→ no certificate, as before) on a constraint explosion or an
       integer grown implausibly large, rather than chase a pathological system *)
    let big = 1 lsl 40 in
    let huge c = abs c.cst > big || List.exists (fun (_, k) -> abs k > big) c.vars in
    let rec loop cons =
      match List.find_opt (fun c -> c.vars = [] && c.cst >= 1) cons with
      | Some c -> Some (c.org, c.cst)
      | None ->
        begin match pick_atom cons with
        | None -> None
        | Some v ->
          let pos = List.filter (fun c -> cv v c > 0) cons in
          let neg = List.filter (fun c -> cv v c < 0) cons in
          let zero = List.filter (fun c -> cv v c = 0) cons in
          if List.length pos * List.length neg + List.length zero > 4096 then None
          else
            let combos =
              List.concat_map (fun p ->
                List.map (fun n ->
                  let cp = cv v p and cn = cv v n in   (* cp > 0, cn < 0 *)
                  reduce {
                    vars = lin_comb (- cn) p.vars cp n.vars;
                    cst  = (- cn) * p.cst + cp * n.cst;
                    org  = Array.init n_h (fun i -> (- cn) * p.org.(i) + cp * n.org.(i));
                  }) neg) pos
            in
            if List.exists huge combos then None else loop (zero @ combos)
        end
    in
    match loop cons0 with
    | None -> None
    | Some (org, c) -> build_cert org c
  end
