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
