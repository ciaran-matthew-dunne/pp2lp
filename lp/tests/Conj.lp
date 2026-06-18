// Tests for rules/Conj.lp (snoc-list 𝕃* conjunction).
require open pp2lp.Prelude;

symbol t_AND1 (ps : 𝕃* o) (P R : Prop)
  (h1 : π (¬ P ⇒ R)) (h2 : π (¬ ⋀ ps ⇒ R)) : π (¬ ⋀ (ps ∷ P) ⇒ R) ≔ AND1 h1 h2;
symbol t_AND2 (ps : 𝕃* o) (P : Prop) (h : π (⋀ ps ⇒ ¬ P)) : π (¬ ⋀ (ps ∷ P)) ≔ AND2 h;
symbol t_AND3 (ps : 𝕃* o) (P R : Prop) (h : π (⋀ ps ⇒ (P ⇒ R))) : π (⋀ (ps ∷ P) ⇒ R) ≔ AND3 h;
symbol t_AND4 (ps : 𝕃* o) (P : Prop) (h1 : π P) (h2 : π (⋀ ps)) : π (⋀ (ps ∷ P)) ≔ AND4 h1 h2;
symbol t_AND5 (C C' r : Prop) (fwd : π C → π C') (hsub : π (C' ⇒ r)) : π (C ⇒ r) ≔ AND5 fwd hsub;

// _1 (Result-form) variants
symbol t_AND1_1 (ps : 𝕃* o) (P R : Prop)
  (r1 : Res (¬ P ⇒ R)) (r2 : Res (¬ ⋀ ps ⇒ R)) : Res (¬ ⋀ (ps ∷ P) ⇒ R) ≔ AND1_1 r1 r2;
symbol t_AND2_1 (ps : 𝕃* o) (P : Prop) (r : Res (⋀ ps ⇒ ¬ P)) : Res (¬ ⋀ (ps ∷ P)) ≔ AND2_1 r;
symbol t_AND3_1 (ps : 𝕃* o) (P R : Prop) (r : Res (⋀ ps ⇒ (P ⇒ R))) : Res (⋀ (ps ∷ P) ⇒ R) ≔ AND3_1 r;
symbol t_AND4_1 (ps : 𝕃* o) (P : Prop) (r1 : Res P) (r2 : Res (⋀ ps)) : Res (⋀ (ps ∷ P)) ≔ AND4_1 r1 r2;
symbol t_AND5_1 (C C' r : Prop) (fwd : π C → π C') (bwd : π C' → π C) (rr : Res (C' ⇒ r))
  : Res (C ⇒ r) ≔ AND5_1 fwd bwd rr;
