// lemmas/Tuple.lp — derived facts about Tuple and the n-ary quantifiers.
// Proved from B.lp's eta_motive, the quantifier bridges, and propExt.
require open pp2lp.B;

// Tuple η, via ind_Tuple + eta_motive: direct induction on Tuple (+1 n) fails
// (the index is a non-variable +1 n), so use a total motive that is ⊤ at index 0
// and the η statement at a successor.
opaque symbol tuple_eta_gen : Π m (v : Tuple m), π (eta_motive m v) ≔
begin
  refine ind_Tuple (λ m v, eta_motive m v) _ _
  { refine ⊤ᵢ }
  { assume m t ih x; refine eq_refl _ }
end;

opaque symbol tuple_eta [n] (v : Tuple (+1 n)) : π (((init v) ⨾ (prj _0 v)) = v) ≔
begin assume n v; refine tuple_eta_gen (+1 n) v end;

// Round-trip for the inserted slot: `prj k (ins k x v) = x`.  `ins_prj` (B.lp)
// only computes for concrete indices, so the abstract-k fact is proved by
// induction; the offset accumulator generalises so the (j+1,k+1) recursion closes.
opaque symbol ins_prj_diag [n] : Π k o x (v : Tuple n), π (ins_prj o k k x v = x) ≔
begin
  assume n;
  induction
  { assume o x v; simplify; reflexivity }
  { assume k ih o x v; simplify; refine ih (+1 o) x v }
end;

opaque symbol prj_ins [n] (k : ℕ) (x : τ ι) (v : Tuple n) : π (prj k (ins k x v) = x) ≔
begin assume n k x v; simplify; refine ins_prj_diag k _0 x v end;

// ---- tcat round-trip: take/drop recover the parts of an appended tuple ----
// Proved by induction on the first tuple (ind_Tuple), so `tcat (t ⨾ x) y` exposes
// a `⨾` and take/drop reduce.  Lemmas (not rewrite rules): a `take (tcat …) ↪ …`
// rule would overlap take's _0/⨾ cases.
opaque symbol take_tcat [k m] (w : Tuple k) (y : Tuple m)
  : π (take [k] [m] (tcat w y) = w) ≔
begin
  assume k m w y;
  have gen : Π j (w' : Tuple j), π (take [j] [m] (tcat w' y) = w')
    { refine ind_Tuple (λ j w', take [j] [m] (tcat w' y) = w') _ _
      { simplify; reflexivity }
      { assume j t ih x; simplify; rewrite ih; reflexivity } };
  refine gen k w
end;

opaque symbol drop_tcat [k m] (w : Tuple k) (y : Tuple m)
  : π (drop [k] [m] (tcat w y) = y) ≔
begin
  assume k m w y;
  have gen : Π j (w' : Tuple j), π (drop [j] [m] (tcat w' y) = y)
    { refine ind_Tuple (λ j w', drop [j] [m] (tcat w' y) = y) _ _
      { simplify; reflexivity }
      { assume j t ih x; simplify; refine ih } };
  refine gen k w
end;

// Transport a curried binary predicate across the round-trip, both directions.
// These are the *reconstruction* core shared by ALL1/ALL4/XST2/XST3: there is no
// `rewrite … in h`, so the take_tcat/drop_tcat equalities are pushed through with
// nested `ind_eq` (Leibniz) instead.
opaque symbol tcat_recon [n] (P : Tuple n → Tuple 1 → Prop)
  (w : Tuple n) (y : Tuple 1)
  : π (P (take [n] [1] (tcat w y)) (drop [n] [1] (tcat w y))) → π (P w y) ≔
begin
  assume n P w y h;
  refine ind_eq (eq_sym (drop_tcat w y)) (λ z, P w z)
    (ind_eq (eq_sym (take_tcat w y)) (λ z, P z (drop [n] [1] (tcat w y))) h)
end;

opaque symbol tcat_recon_inv [n] (P : Tuple n → Tuple 1 → Prop)
  (w : Tuple n) (y : Tuple 1)
  : π (P w y) → π (P (take [n] [1] (tcat w y)) (drop [n] [1] (tcat w y))) ≔
begin
  assume n P w y h;
  refine ind_eq (drop_tcat w y) (λ z, P (take [n] [1] (tcat w y)) z)
    (ind_eq (take_tcat w y) (λ z, P z y) h)
end;

// m-general reconstruction transports (`take_tcat`/`drop_tcat` are already
// m-general; these just lift the `Tuple 1` specialisation).  Feed `!!_split_eq_m`
// below, used by the NRM8/NRM9 chain bridges (rules/Res.lp).
opaque symbol tcat_recon_m [n m] (P : Tuple n → Tuple m → Prop)
  (w : Tuple n) (y : Tuple m)
  : π (P (take [n] [m] (tcat w y)) (drop [n] [m] (tcat w y))) → π (P w y) ≔
begin
  assume n m P w y h;
  refine ind_eq (eq_sym (drop_tcat w y)) (λ z, P w z)
    (ind_eq (eq_sym (take_tcat w y)) (λ z, P z (drop [n] [m] (tcat w y))) h)
end;

opaque symbol tcat_recon_inv_m [n m] (P : Tuple n → Tuple m → Prop)
  (w : Tuple n) (y : Tuple m)
  : π (P w y) → π (P (take [n] [m] (tcat w y)) (drop [n] [m] (tcat w y))) ≔
begin
  assume n m P w y h;
  refine ind_eq (drop_tcat w y) (λ z, P (take [n] [m] (tcat w y)) z)
    (ind_eq (take_tcat w y) (λ z, P z y) h)
end;

// ---- compound ↔ nested binder equality (§A.7–8 regroupement) ----
// The single fact behind every curried merge rule: a compound `Tuple (n ++ 1)`
// binder splitting v with take/drop is *equal* (propExt) to the nested
// `Tuple n × Tuple 1` binder.  ALL1/2/4 and XST1–4 are one-line transports of this
// (via imp_cong_l / not_cong).  The curried P (`P w y`, a pattern) is why the
// emitter can `refine ALLn _` with P inferred — see rules/All.lp, rules/Xst.lp.
//
// Forward (compound → nested) is *reconstruction* for `!!` (instantiate the
// compound at `tcat w y`) and *projection* for `??`; backward flips.  Each
// direction does the hard half once.
opaque symbol !!_split_eq [n] (P : Tuple n → Tuple 1 → Prop)
  : π ((`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))
       = (`!! w : Tuple n, `!! y : Tuple 1, P w y)) ≔
begin
  assume n P;
  refine propExt _ _ _ _
  { assume hC;
    refine pi_to_!! _ _; assume w;
    refine pi_to_!! _ _; assume y;
    refine tcat_recon P w y
      (!!_to_pi (λ v, P (take [n] [1] v) (drop [n] [1] v)) hC (tcat w y)) }
  { assume hN;
    refine pi_to_!! _ _; assume v;
    refine !!_to_pi (λ y, P (take [n] [1] v) y)
             (!!_to_pi (λ w, `!! y : Tuple 1, P w y) hN (take [n] [1] v))
             (drop [n] [1] v) }
end;

// m-general split (the `Tuple 1` `!!_split_eq` for any inner arity m).  Same
// proof, with the m-general `tcat_recon_m`.  Used by the NRM8/NRM9 chain bridges.
opaque symbol !!_split_eq_m [n m] (P : Tuple n → Tuple m → Prop)
  : π ((`!! v : Tuple (n ++ m), P (take [n] [m] v) (drop [n] [m] v))
       = (`!! w : Tuple n, `!! y : Tuple m, P w y)) ≔
begin
  assume n m P;
  refine propExt _ _ _ _
  { assume hC;
    refine pi_to_!! _ _; assume w;
    refine pi_to_!! _ _; assume y;
    refine tcat_recon_m P w y
      (!!_to_pi (λ v, P (take [n] [m] v) (drop [n] [m] v)) hC (tcat w y)) }
  { assume hN;
    refine pi_to_!! _ _; assume v;
    refine !!_to_pi (λ y, P (take [n] [m] v) y)
             (!!_to_pi (λ w, `!! y : Tuple m, P w y) hN (take [n] [m] v))
             (drop [n] [m] v) }
end;

opaque symbol ??_split_eq [n] (P : Tuple n → Tuple 1 → Prop)
  : π ((`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))
       = (`?? w : Tuple n, `?? y : Tuple 1, P w y)) ≔
begin
  assume n P;
  refine propExt _ _ _ _
  { assume hC;
    refine pi_to_??_elim (λ v, P (take [n] [1] v) (drop [n] [1] v)) _ hC;
    assume v hv;
    refine pi_to_??_intro (λ w, `?? y : Tuple 1, P w y) (take [n] [1] v)
             (pi_to_??_intro (λ y, P (take [n] [1] v) y) (drop [n] [1] v) hv) }
  { assume hN;
    refine pi_to_??_elim (λ w, `?? y : Tuple 1, P w y) _ hN;
    assume w hw;
    refine pi_to_??_elim (λ y, P w y) _ hw;
    assume y hy;
    refine pi_to_??_intro (λ v, P (take [n] [1] v) (drop [n] [1] v)) (tcat w y)
             (tcat_recon_inv P w y hy) }
end;

// Pointwise equality lifts to !! equality.
opaque symbol !!_cong [n] [P R : Tuple n → Prop]
  : (Π v : Tuple n, π (P v = R v))
  → π ((`!! v, P v) = (`!! v, R v)) ≔
begin
  assume n P R h;
  refine propExt _ _ _ _
  { assume hP; refine pi_to_!! R (λ v, =⇒ (h v) (!!_to_pi P hP v)) }
  { assume hR; refine pi_to_!! P (λ v, =⇒ (eq_sym (h v)) (!!_to_pi R hR v)) }
end;

// Pointwise equality lifts to ?? equality.
opaque symbol ??_cong [n] [P R : Tuple n → Prop]
  : (Π v : Tuple n, π (P v = R v))
  → π ((`?? v, P v) = (`?? v, R v)) ≔
begin
  assume n P R h;
  refine propExt _ _ _ _
  { assume hP; refine pi_to_??_elim P
      (λ v hPv, pi_to_??_intro R v (=⇒ (h v) hPv)) hP }
  { assume hR; refine pi_to_??_elim R
      (λ v hRv, pi_to_??_intro P v (=⇒ (eq_sym (h v)) hRv)) hR }
end;

// Drop a constant !!-binder (Tuple-n analogue of PropExt's ∀_const, via inh_tuple).
opaque symbol !!_const [n] (P : Prop)
  : π ((`!! _ : Tuple n, P) = P) ≔
begin
  assume n P;
  refine propExt _ _ _ _
  { assume h; refine !!_to_pi (λ _ : Tuple n, P) h (inh_tuple [n]) }
  { assume h; refine pi_to_!! (λ _ : Tuple n, P) (λ _, h) }
end;

// ♢ and ♡ equal !! (from the bridges, via propExt).
opaque symbol ♢_eq_!! [n] (P : Tuple n → Prop)
  : π ((`♢ v, P v) = (`!! v, P v)) ≔
begin
  assume n P;
  refine propExt _ _ _ _
  { assume h; refine pi_to_!! P (♢_to_pi P h) }
  { assume h; refine pi_to_♢ P (!!_to_pi P h) }
end;

opaque symbol ♡_eq_!! [n] (P : Tuple n → Prop)
  : π ((`♡ v, P v) = (`!! v, P v)) ≔
begin
  assume n P;
  refine propExt _ _ _ _
  { assume h; refine pi_to_!! P (♡_to_pi P h) }
  { assume h; refine pi_to_♡ P (!!_to_pi P h) }
end;

// ============ NRM20 slot-surgery reassembly metatheory ============

// prj-based bounded agreement: agree' off c a b  ≡  ⋀_{i<c} (prj (off+i) a = prj (off+i) b).
// Recurses on the count c, peeling the LOW slot `off` (so it never touches the
// ⨾-spine and stays computable on an opaque `ins`-term).
symbol agree' [M] : ℕ → ℕ → Tuple M → Tuple M → Prop;
rule agree' _ _0      _  _  ↪ ⊤
with agree' $off (+1 $c) $a $b ↪ ((prj $off $a = prj $off $b) ∧ agree' (+1 $off) $c $a $b);

// Tuple 0 is uniquely `unit` (eta_motive trick; direct η at index 0 is ⊤).
symbol tup0_mot : Π m, Tuple m → Prop;
rule tup0_mot _0     $b ↪ ($b = unit)
with tup0_mot (+1 _) _  ↪ ⊤;
opaque symbol tup0_unit (b : Tuple 0) : π (b = unit) ≔
begin
  assume b;
  have gen : Π m (v : Tuple m), π (tup0_mot m v)
    { refine ind_Tuple (λ m v, tup0_mot m v) _ _
      { refine eq_refl unit }
      { assume m t ih x; refine ⊤ᵢ } };
  refine gen 0 b
end;

// Shift: agreement on slots [off+1 ..) of a,b is agreement on slots [off ..) of
// init a, init b (since prj j (init v) ↪ prj (+1 j) v).  Induct on the count.
opaque symbol agree_shift [M] : Π c o (a b : Tuple (+1 M)),
  π (agree' (+1 o) c a b) → π (agree' o c (init a) (init b)) ≔
begin
  assume M;
  induction
  { assume o a b h; refine ⊤ᵢ }
  { assume c ih o a b h;
    refine ∧ᵢ (∧ₑ₁ h) (ih (+1 o) a b (∧ₑ₂ h)) }
end;

// Tuple extensionality: agreement on all M slots forces equality.
opaque symbol prj_ext : Π M (a b : Tuple M), π (agree' 0 M a b) → π (a = b) ≔
begin
  have gen : Π M (a : Tuple M), π (`!! b, agree' 0 M a b ⇒ (a = b))
    { refine ind_Tuple (λ M a, `!! b : Tuple M, agree' 0 M a b ⇒ (a = b)) _ _
      { refine pi_to_!! _ (λ b _, eq_sym (tup0_unit b)) }
      { assume m t ih x;
        refine pi_to_!! _ (λ b hag, _);
        have hx : π (x = prj 0 b) { refine ∧ₑ₁ hag };
        have ht : π (t = init b)
          { refine !!_to_pi (λ b', agree' 0 m t b' ⇒ (t = b')) ih (init b)
                            (agree_shift m 0 (t ⨾ x) b (∧ₑ₂ hag)) };
        refine ind_eq (eq_sym (tuple_eta b)) (λ z, (t ⨾ x) = z) _;
        rewrite ht; rewrite hx; reflexivity } };
  assume M a b h; refine !!_to_pi (λ b', agree' 0 M a b' ⇒ (a = b')) (gen M a) b h
end;

// ---- ℕ-addition on the right (++ recurses on the left, so these aren't defeq) ----
opaque symbol add_0_r : Π a, π ((a ++ 0) = a) ≔
begin
  induction
  { reflexivity }
  { assume a ih; simplify; rewrite ih; reflexivity }
end;

opaque symbol add_succ_r : Π a b, π ((a ++ (+1 b)) = (+1 (a ++ b))) ≔
begin
  induction
  { assume b; reflexivity }
  { assume a ih b; simplify; rewrite (ih b); reflexivity }
end;

// ---- rm_prj characterisations: querying a slot below vs at-or-above the removed one ----
// Below: prj i (rm K v) = prj i v  when i < K  (here K = i ++ (+1 d) > i).
opaque symbol rm_below [n] : Π i lo d (v : Tuple (+1 n)),
  π (rm_prj lo i (i ++ (+1 d)) v = prj (lo ++ i) v) ≔
begin
  assume n;
  induction
  { assume lo d v; simplify; rewrite (add_0_r lo); reflexivity }
  { assume i ih lo d v; simplify; rewrite (add_succ_r lo i); refine ih (+1 lo) d v }
end;

// At-or-above: prj i (rm K v) = prj (+1 i) v  when i ≥ K  (here i = K ++ excess).
opaque symbol rm_above [n] : Π K lo i (v : Tuple (+1 n)),
  π (rm_prj lo (K ++ i) K v = prj (+1 (lo ++ (K ++ i))) v) ≔
begin
  assume n;
  induction
  { assume lo i v; simplify; reflexivity }
  { assume K ih lo i v; simplify; rewrite (add_succ_r lo (K ++ i)); refine ih (+1 lo) i v }
end;

// ---- the trichotomy: prj j (ins k (prj k v) (rm k v)) = prj j v, with offset accumulator ----
// ins_prj's (+1,+1) recursion bumps the offset o, and o++k / o++j track the shifted
// query/insert positions so the IH (at o := +1 o) closes the diagonal-decoupled recursion.
opaque symbol agree_gen [n] : Π j o k (v : Tuple (+1 n)),
  π (ins_prj o j k (prj (o ++ k) v) (rm (o ++ k) v) = prj (o ++ j) v) ≔
begin
  assume n;
  induction
  { assume o; induction
    { assume v; simplify; reflexivity }
    { assume k kih v; simplify; rewrite (add_0_r o); refine rm_below o 0 k v } }
  { assume j ih o; induction
    { assume v; simplify; rewrite (add_0_r o); rewrite (add_succ_r o j); refine rm_above o 0 j v }
    { assume k kih v; simplify; rewrite (add_succ_r o k); rewrite (add_succ_r o j); refine ih (+1 o) k v } }
end;

// ---- assemble per-slot agreement into bounded agreement, then reassembly ----
opaque symbol agree_build [M] : Π count o (a b : Tuple M),
  (Π j, π (prj j a = prj j b)) → π (agree' o count a b) ≔
begin
  assume M;
  induction
  { assume o a b hag; refine ⊤ᵢ }
  { assume count ih o a b hag; refine ∧ᵢ (hag o) (ih (+1 o) a b hag) }
end;

// THE GOAL: ins k (prj k v) (rm k v) = v  (slot-surgery reassembly, k abstract).
opaque symbol reassemble [n] : Π k (v : Tuple (+1 n)),
  π ((ins k (prj k v) (rm k v)) = v) ≔
begin
  assume n k v;
  refine prj_ext (+1 n) (ins k (prj k v) (rm k v)) v
    (agree_build (+1 n) 0 (ins k (prj k v) (rm k v)) v (λ j, agree_gen j 0 k v))
end;

// ---- nrm20_eq: the NRM20 chain-form soundness bridge (BIG = SMALL), no postulate ----
opaque symbol nrm20_eq [n] (k : ℕ) [qs : Tuple (+1 n) → 𝕃* o] [Q : Prop] (E : Tuple n → τ ι)
  : π (((`♡ v : Tuple (+1 n), ¬ ⋀ (qs v ∷ (prj k v = E (rm k v)))) ⇒ Q)
       = ((`♡ v' : Tuple n, ¬ ⋀ (qs (ins k (E v') v'))) ⇒ Q)) ≔
begin
  assume n k qs Q E;
  have hpred : π ((`♡ v : Tuple (+1 n), ¬ ⋀ (qs v ∷ (prj k v = E (rm k v))))
                  = (`♡ v' : Tuple n, ¬ ⋀ (qs (ins k (E v') v'))))
    { refine propExt _ _
        (λ hbig, pi_to_♡ (λ v' : Tuple n, ¬ ⋀ (qs (ins k (E v') v')))
           (λ v' hq, ♡_to_pi (λ v, ¬ ⋀ (qs v ∷ (prj k v = E (rm k v)))) hbig (ins k (E v') v')
             (⋀_intro hq (prj_ins k (E v') v'))))
        (λ hsmall, pi_to_♡ (λ v : Tuple (+1 n), ¬ ⋀ (qs v ∷ (prj k v = E (rm k v))))
           (λ v hcon, ♡_to_pi (λ v', ¬ ⋀ (qs (ins k (E v') v'))) hsmall (rm k v)
             (ind_eq (ind_eq (eq_sym (⋀_last hcon)) (λ z, (ins k z (rm k v)) = v) (reassemble k v))
                     (λ z, ⋀ (qs z)) (⋀_init hcon)))) };
  rewrite hpred; reflexivity
end;
