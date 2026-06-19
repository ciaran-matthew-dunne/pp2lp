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

(* Whether a literal atom folds into the reified constant.  Only `Nat` literals
   do: they fit OCaml's native `int`, so [lin_normal] sums them into the constant
   and [reify] emits them as `Llit`.  A `BigNat` (apero's 2⁶⁴ bounds) overflows a
   native int, so it is left a symbolic atom — reified as a `Lvar`, compared by
   index, never summed — hence false here. *)
let is_foldable_lit = function Nat _ -> true | _ -> false

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
  (* literal-coefficient product `n*x` (rendered `mult`): integer-valued by mult_def. *)
  | SetOp ("prod", [ (Nat _ as k); x ]) | SetOp ("prod", [ x; (Nat _ as k) ]) ->
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
  | Nat 0 -> Some []
  (* `prod(k, e)` / `prod(e, k)` with a literal coefficient k is arithmetic scaling
     k·e (a literal can't be a Cartesian operand): scale e's atom coefficients by k.
     Before the `is_atom_exp` catch — a `prod` is a SetOp, hence an atom otherwise. *)
  | SetOp ("prod", [ Nat k; a ]) | SetOp ("prod", [ a; Nat k ]) ->
    Option.map (List.map (fun (x, s) -> (x, k * s))) (flatten_signed a)
  | AOp (Add, a, b) -> app (flatten_signed a) (flatten_signed b)
  | AOp (Sub, a, b) -> app (flatten_signed a) (negate (flatten_signed b))
  | Neg a -> negate (flatten_signed a)        (* — over any sub-expr (incl. scaled prod) *)
  | _ when is_atom_exp e -> Some [ (e, 1) ]
  | _ -> None

let signed_exp (a, s) = if s >= 0 then a else Neg a

(* Left-nested sum of a (non-empty) signed-atom list, as a PP expression. *)
let lfold_exp = function
  | [] -> Nat 0
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
   fold into the constant, every other atom (incl `BigNat`) stays symbolic and is
   compared structurally.  Two exprs denote the same value iff their [lin_normal]s
   are equal.  None if [e] is not `+`/`−`-linear. *)
let lin_normal e : ((exp * int) list * int) option =
  match flatten_signed e with
  | None -> None
  | Some atoms ->
    let const =
      List.fold_left (fun c (a, s) -> match a with Nat n -> c + (s * n) | _ -> c)
        0 atoms in
    let net =
      List.fold_left (fun acc (a, s) ->
        match a with
        | Nat _ -> acc
        | _ ->
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
    | SetOp ("prod", [ Nat _; a ]) | SetOp ("prod", [ a; Nat _ ]) -> go acc a
    | Nat _ -> acc
    | _ when is_atom_exp e -> if List.mem e acc then acc else acc @ [ e ]
    | _ -> acc
  in
  List.fold_left go [] es

(* Reify a linear expr to an `LE` term, mirroring its `+`/`−`/`neg` structure so
   `den ρ (reify e) ≡ to_int e` by reduction.  `Nat` → `Llit`; any other atom →
   `Lvar <its index>`. *)
let rec reify idx e : L.term =
  match e with
  | AOp (Add, a, b) -> L.App (L.Name "Ladd", [ reify idx a; reify idx b ])
  | AOp (Sub, a, b) ->
    L.App (L.Name "Ladd", [ reify idx a; L.App (L.Name "Lneg", [ reify idx b ]) ])
  | Neg a -> L.App (L.Name "Lneg", [ reify idx a ])
  | SetOp ("prod", [ Nat k; a ]) | SetOp ("prod", [ a; Nat k ]) ->
    L.App (L.Name "Lmul", [ z_dec (string_of_int k); reify idx a ])
  | Nat n -> L.App (L.Name "Llit", [ z_dec (string_of_int n) ])
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
        [ L.Exp (env, Nat c); L.Exp (env, Nat 0); L.Name "_h";
          L.Name "\xe2\x8a\xa4\xe1\xb5\xa2" (* ⊤ᵢ *) ]))

(* `π (e1 = e2)` for two `+`/`−` exprs denoting the same value: the `e1 = e2`
   fast path is `eq_refl`, otherwise reflect onto ℤ ([reflect_eq]).  None if
   either is non-linear or they are not equal. *)
let prove_sum_eq env e1 e2 : L.term option =
  if e1 = e2 then Some (L.App (L.Name "eq_refl", [ L.Exp (env, e1) ]))
  else reflect_eq env e1 e2

(* `π (e = 𝟎)` when [e]'s atoms cancel to nothing: reflect against the literal 0
   (`Exp (Nat 0) ≡ 𝟎`). *)
let prove_sum_zero env e : L.term option = reflect_eq env e (Nat 0)

(* `π (e > 𝟎)` when [e] cancels/folds to a positive literal c: transport
   `¬(from_int c ≤ 𝟎)` (`positive_lit`) along the reflected `e = from_int c`. *)
let prove_gt_zero env e : L.term option =
  match lin_normal e with
  | Some ([], c) when c >= 1 ->
    (match reflect_eq env e (Nat c) with
     | Some e_eq_c ->                                  (* e_eq_c : e = from_int c *)
       Some (L.App (L.Name "=\xe2\x87\x92",            (* =⇒ : π (A = B) → π A → π B *)
         [ L.App (L.Name "eq_sym",
             [ L.App (L.Name "not_cong",
                 [ L.App (L.Name "leq_zero_eq", [ e_eq_c ]) ]) ]);
           positive_lit env c ]))
     | None -> None)
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
  (* Per-hypothesis multiplier cap.  A `−x ≤ 𝟎` cancelling a `k·x` needs λ = k, so
     coefficient-k Farkas wants a cap ≥ k; the search is O((cap+1)^n_h), so raise
     it only when there are few hypotheses (the coefficient cases have 2). *)
  let cap = if n_h <= 2 then 16 else if n_h <= 4 then 10 else arith_max_lambda in
  let rec search i =
    if i = n_h then
      if Array.exists (fun l -> l > 0) lambdas
      then Option.map (fun c -> (Array.copy lambdas, c)) (pos_const lambdas)
      else None
    else
      let rec try_l l =
        if l > cap then None
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
