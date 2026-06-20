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
