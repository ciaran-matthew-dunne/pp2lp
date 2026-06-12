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
  | Var _ | Nat _ | App _ | SetImage _ | Inter _ | Union _ | Range _
  | Maplet _ | Inverse _ | SetLit _ | DomRestrict _ | RanRestrict _ -> true
  | AOp _ | Neg _ -> false

(* Numeric literals 2 ≤ k ≤ [lit_unfold_max] flatten to k copies of the
   `𝟏`-atom, so PP's solver-side literal folding (`1 + 9 → 10` in AR3's
   `𝟏 − a` sub-premise) is invisible to the multiset comparison and the
   generated proofs: `int_lit k ≡ 𝟏 + int_lit (k−1)` definitionally, so the
   recursive [normalize] proof is checked by conversion.  Bounded: a big
   literal must never be unfolded (decimal numerals exist precisely to keep
   them folded — whnf of a big `int_lit` blows up), beyond the cap the
   literal stays an opaque atom as before. *)
let lit_unfold_max = 64

(* Flatten a `+`/`−` expression to its ordered signed-atom list, pushing unary
   `—` down to the atoms (— distributes over + and is involutive); None if a
   non-arithmetic node blocks it.  Mirrors [normalize]'s recursion exactly, so
   a match here is precisely what [normalize] can prove. *)
let rec flatten_signed e : (exp * int) list option =
  let negate = Option.map (List.map (fun (a, s) -> (a, -s))) in
  let app o p = match o, p with Some a, Some b -> Some (a @ b) | _ -> None in
  match e with
  | Nat 0 | Neg (Nat 0) -> Some []
  | Nat k when k >= 2 && k <= lit_unfold_max ->
    Some (List.init k (fun _ -> (Nat 1, 1)))
  | Neg (Nat k) when k >= 2 && k <= lit_unfold_max ->
    Some (List.init k (fun _ -> (Nat 1, -1)))
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
      | x :: (y :: _ as tl) -> if compare x y > 0 then Some i else go (i + 1) tl
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
  | _, [] -> L.App (L.Name "add_zero", [ ex (lfold_exp la) ])
  | [], _ -> L.App (L.Name "zero_add", [ ex (lfold_exp lb) ])
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
  (* Literal unfold (see [lit_unfold_max]): the printer renders `Nat k` as the
     left-nested 𝟏-sum `(𝟏 + 𝟏 + … + 𝟏)` — exactly `lfold` of k 𝟏-atoms — so
     the decomposition is `eq_refl` (the two renderings parse to the same
     term).  `— k` goes through the `Neg (Add …)` case (opp_add to the
     leaves), stated at the explicit sum, which parses identically.  `𝟎`
     contributes NO atom (`lfold [] ≡ 𝟎`, refl; `— 𝟎` via neg_zero) — as an
     opaque atom it would block cancellation (`1 − 0` vs `1`). *)
  | Nat 0 -> Some ([], refl e)
  | Neg (Nat 0) -> Some ([], L.App (L.Name "neg_zero", []))
  | Nat k when k >= 2 && k <= lit_unfold_max ->
    Some (List.init k (fun _ -> (Nat 1, 1)), refl e)
  | Neg (Nat k) when k >= 2 && k <= lit_unfold_max ->
    normalize env (Neg (lfold_exp (List.init k (fun _ -> (Nat 1, 1)))))
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
     | Some (la, pa) -> Some (la, trans (L.App (L.Name "neg_neg", [ ex a ])) pa)
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
                 (trans (congR pf neg_add_a) (L.App (L.Name "add_zero", [ ex pf ]))) in
    fold_congL core suf
  | [] ->
    (match suf with
     | [] -> neg_add_a                                            (* —a + a = 𝟎 = lfold [] *)
     | s0 :: rest ->
       (* (—a + a) + s0 = s0, then congL the rest. *)
       let s0e = signed_exp s0 in
       let core = trans (congL s0e neg_add_a) (L.App (L.Name "zero_add", [ ex s0e ])) in
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

(* `π (e1 = e2)` for two `+`/`−` expressions denoting the same signed-atom
   multiset *after additive cancellation* (`n + —n = 𝟎`); None if either is
   unsupported or the reduced multisets differ.  Each side goes [normalize] (—
   to leaves) → sort (a permutation) → [reduce_cancel] (drop ± pairs); the two
   reduced+sorted lists are identical iff equal as multisets. *)
let prove_sum_eq env e1 e2 : L.term option =
  match normalize env e1, normalize env e2 with
  | Some (l1, p1), Some (l2, p2) ->
    let r1, c1 = reduce_cancel env (List.sort compare l1) in
    let r2, c2 = reduce_cancel env (List.sort compare l2) in
    if r1 = r2 then
      let trans p q = L.App (L.Name "eq_trans", [ p; q ]) in
      let sym p = L.App (L.Name "eq_sym", [ p ]) in
      (* e1 = lfold l1 = lfold(sort l1) = lfold r1 = lfold r2
            = lfold(sort l2) = lfold l2 = e2 *)
      Some (trans p1 (trans (prove_eq_lnested env l1) (trans c1
              (trans (sym c2)
                (trans (sym (prove_eq_lnested env l2)) (sym p2))))))
    else None
  | _ -> None

(* `π (e = 𝟎)` when [e]'s signed atoms cancel to the empty multiset (e.g.
   `—a + a`, `—(—a) − a`).  [prove_sum_eq … (Nat 0)] can't prove this — `𝟎`
   normalises to the *atom* `0`, not the empty list, so the multisets differ —
   so chain the normalise / sort / cancel proofs directly: the cancelled list
   folds to `lfold [] ≡ 𝟎`. *)
let prove_sum_zero env e : L.term option =
  match normalize env e with
  | Some (l, p) ->
    let r, c = reduce_cancel env (List.sort compare l) in
    if r = [] then
      let trans p q = L.App (L.Name "eq_trans", [ p; q ]) in
      Some (trans p (trans (prove_eq_lnested env l) c))
    else None
  | None -> None

(* `π (e > 𝟎)` (= `π (¬(e ≤ 𝟎))`) when [e] cancels to a positive literal k:
   `¬(k ≤ 𝟎)` (one_not_leq_zero for k=1; for k≥2, `𝟏 ≤ k ≤ 𝟎` is absurd via the
   chained `leq_plus_one`), transported along the generated `e = k`.  Used by
   AR4, whose `(E+F) > 𝟎` premise has `E + F` cancelling to a literal. *)
let prove_gt_zero env e : L.term option =
  let rec one_leq_lit c =                         (* π (𝟏 ≤ c·𝟏), c ≥ 1 *)
    if c <= 1 then L.App (L.Name "leq_refl", [ L.Exp (env, Nat 1) ])
    else
      L.App (L.Name "leq_trans",
        [ L.Exp (env, Nat 1); L.Exp (env, Nat (c - 1)); L.Exp (env, Nat c);
          one_leq_lit (c - 1);
          L.App (L.Name "leq_plus_one", [ L.Exp (env, Nat (c - 1)) ]) ])
  in
  let lit_not_leq_zero c =                         (* π (¬(c·𝟏 ≤ 𝟎)) *)
    if c = 1 then L.Name "one_not_leq_zero"
    else
      L.Lambda ("_hk", None,
        L.App (L.Name "one_not_leq_zero",
          [ L.App (L.Name "leq_trans",
              [ L.Exp (env, Nat 1); L.Exp (env, Nat c); L.Exp (env, Nat 0);
                one_leq_lit c; L.Name "_hk" ]) ]))
  in
  let rec try_k k =
    if k > 8 then None
    else match prove_sum_eq env e (Nat k) with
      | Some eqpf ->
        Some (L.App (L.Name "=\xe2\x87\x92",        (* =⇒ : π (A = B) → π A → π B *)
          [ L.App (L.Name "eq_sym",
              [ L.App (L.Name "not_cong",
                  [ L.App (L.Name "leq_zero_eq", [ eqpf ]) ]) ]);
            lit_not_leq_zero k ]))
      | None -> try_k (k + 1)
  in
  try_k 1

(* ---- ARITH: Farkas-style linear-combination contradiction ----

   PP's linear solver closes ⊥ from the `eᵢ ≤ 𝟎` hypotheses in scope without
   recording a certificate.  Reconstruct one: search small nonnegative
   multipliers λᵢ with Σ λᵢ·eᵢ = 𝟏 — every non-constant atom cancels and the
   constant lands on exactly one 𝟏 ([flatten_signed] unfolds literals to
   𝟏-atoms, so "the constant" is the net 𝟏-count) — then emit

     one_not_leq_zero (leq_subst_l (𝟏 = Σ…) (add_leq_zero … hᵢ …))

   with the Σ-equality generated by [prove_sum_eq] (no `trust`).  Combinations
   summing to a constant ≥ 2 exist in principle (no λ with target 𝟏 then);
   they are out of scope until a trace needs one. *)
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
  (* the combination's net vector must be a single positive constant
     (every non-𝟏 atom cancels); returns that constant *)
  let pos_const lambdas =
    let total = Hashtbl.create 8 in
    Array.iteri (fun j v ->
      if lambdas.(j) > 0 then
        List.iter (fun (a, c) ->
          let cur = try Hashtbl.find total a with Not_found -> 0 in
          Hashtbl.replace total a (cur + lambdas.(j) * c)) v) vecs;
    let ok = Hashtbl.fold (fun a c ok -> ok && (c = 0 || a = Nat 1))
               total true in
    let const = try Hashtbl.find total (Nat 1) with Not_found -> 0 in
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
  (* π (𝟏 ≤ c·𝟏) for the literal c ≥ 1: chain leq_plus_one up the (left-
     nested, definitionally `lit (k−1) + 𝟏`) literal renders. *)
  let rec one_leq_lit c =
    if c <= 1 then L.App (L.Name "leq_refl", [ L.Exp (env, Nat 1) ])
    else
      L.App (L.Name "leq_trans",
        [ L.Exp (env, Nat 1); L.Exp (env, Nat (c - 1)); L.Exp (env, Nat c);
          one_leq_lit (c - 1);
          L.App (L.Name "leq_plus_one", [ L.Exp (env, Nat (c - 1)) ]) ])
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
              let lit_leq_zero =
                L.App (L.Name "leq_subst_l", [ eqpf; hsum ]) in
              let one_leq_zero =
                if c = 1 then lit_leq_zero
                else
                  L.App (L.Name "leq_trans",
                    [ L.Exp (env, Nat 1); L.Exp (env, Nat c);
                      L.Exp (env, Nat 0);
                      one_leq_lit c; lit_leq_zero ])
              in
              L.Refine (L.Name "one_not_leq_zero", [ one_leq_zero ]))
           (prove_sum_eq env (Nat c) combined))
