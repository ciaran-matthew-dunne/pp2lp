// Soundness of syntactic equality (prd_eq, exp_eq, var_eq).
require open Stdlib.Bool Stdlib.Set Stdlib.Prop Stdlib.Eq Stdlib.FOL Stdlib.String;
require pp2lp.B as B;
require pp2lp.Eq;
require pp2lp.Interp as I;

// ---- var_eq_sound ----

opaque symbol var_eq_sound (x y : B.Var)
  : π (istrue (B.var_eq x y)) → π (x = y) ≔
begin
  assume x;  refine B.ind_Var
    (λ x, `∀ y : τ B.var, istrue (B.var_eq x y) ⇒ (x = y))
    _ _ x
  // case x = id s
  { assume s y; refine B.ind_Var
      (λ y, istrue (B.var_eq (B.id s) y) ⇒ (B.id s = y))
      _ _ y
    // y = id t
    { assume t h; refine feq B.id (I.str_eq_sound s t h) }
    // y = y1 ⨾ y2
    { assume a b c d h; refine ⊥ₑ h } }
  // case x = x1 ⨾ x2
  { assume x1 ih1 x2 ih2 y; refine B.ind_Var
      (λ y, istrue (B.var_eq (x1 B.⨾ x2) y) ⇒ ((x1 B.⨾ x2) = y))
      _ _ y
    // y = id t
    { assume a h; refine ⊥ₑ h }
    // y = y1 ⨾ y2
    { assume y1 ihy1 y2 ihy2 h;
      refine feq2 (λ (a : τ B.var) (b : τ B.var), a B.⨾ b)
        (ih1 y1 (@andₑ₁ (B.var_eq x1 y1) (B.var_eq x2 y2) h))
        (ih2 y2 (@andₑ₂ (B.var_eq x1 y1) (B.var_eq x2 y2) h)) } }
end;

// ---- motives for mutual induction ----

symbol p0 : B.Prd → Prop ≔
  λ P, `∀ Q : τ B.prd, istrue (B.prd_eq P Q) ⇒ (P = Q);

symbol p2 : B.Exp → Prop ≔
  λ E, `∀ F : τ B.exp, istrue (B.exp_eq E F) ⇒ (E = F);

// ---- inner mismatch/trivial branch abbreviations ----
// For Prd outer cases, the inner ind_Prd has motive (λ Q, ...) for Prd
// and (λ e, ⊤) for Exp. We abbreviate the ⊥ₑ and ⊤ᵢ branches.

// Prd-mismatch branches (11 shapes, one per Prd constructor):
// ¬:    λ q iq h, ⊥ₑ h
// ∧∨⇒⇔: λ q1 iq1 q2 iq2 h, ⊥ₑ h
// = ∈:  λ e1 ie1 e2 ie2 h, ⊥ₑ h
// ∀∃♢♡: λ x p ip h, ⊥ₑ h

// Exp-trivial branches (7 shapes, one per Exp constructor):
// #var:    λ x, ⊤ᵢ
// ↦ ×:    λ e1 ie1 e2 ie2, ⊤ᵢ
// 𝒫:      λ e ie, ⊤ᵢ
// big:     ⊤ᵢ
// choice:  λ e ie, ⊤ᵢ
// comp:    λ x p ip, ⊤ᵢ

// For Exp outer cases, the inner ind_Exp has motive (λ e, ⊤) for Prd
// and (λ F, ...) for Exp. Prd-trivial branches:
// ¬:    λ q iq, ⊤ᵢ
// ∧∨⇒⇔: λ q1 iq1 q2 iq2, ⊤ᵢ
// = ∈:  λ e1 ie1 e2 ie2, ⊤ᵢ
// ∀∃♢♡: λ x p ip, ⊤ᵢ

// Exp-mismatch branches:
// #var:    λ x h, ⊥ₑ h
// ↦ ×:    λ e1 ie1 e2 ie2 h, ⊥ₑ h
// 𝒫:      λ e ie h, ⊥ₑ h
// big:     λ h, ⊥ₑ h
// choice:  λ e ie h, ⊥ₑ h
// comp:    λ x p ip h, ⊥ₑ h

// ---- shared case proofs (18 cases) ----

// Helper: split a boolean and with explicit args.
symbol split₁ (a b : 𝔹) (h : π (istrue (a and b))) : π (istrue a) ≔ @andₑ₁ a b h;
symbol split₂ (a b : 𝔹) (h : π (istrue (a and b))) : π (istrue b) ≔ @andₑ₂ a b h;

// ========== Prd constructors ==========

// case ¬ p (unary Prd)
symbol c_neg (p : B.Prd) (ihp : π (p0 p)) : π (p0 (B.¬ p)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq (B.¬ p) Q) ⇒ ((B.¬ p) = Q))
    (λ e, ⊤)
    // ¬ q — match
    (λ q iq h, feq (λ (x : τ B.prd), B.¬ x) (ihp q h))
    // ∧ — mismatch
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    // ∨
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    // ⇒
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    // ⇔
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    // =
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    // ∈
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    // ∀
    (λ x q iq h, ⊥ₑ h)
    // ∃
    (λ x q iq h, ⊥ₑ h)
    // ♢
    (λ x q iq h, ⊥ₑ h)
    // ♡
    (λ x q iq h, ⊥ₑ h)
    // Exp: #var
    (λ x, ⊤ᵢ)
    // ↦
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    // ×
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    // 𝒫
    (λ e ie, ⊤ᵢ)
    // big
    ⊤ᵢ
    // choice
    (λ e ie, ⊤ᵢ)
    // comp
    (λ x p ip, ⊤ᵢ)
    Q;

// case p1 ∧ p2 (binary Prd-Prd)
symbol c_and (p1 : B.Prd) (ih1 : π (p0 p1)) (p2 : B.Prd) (ih2 : π (p0 p2))
  : π (p0 (p1 B.∧ p2)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq (p1 B.∧ p2) Q) ⇒ ((p1 B.∧ p2) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    // ∧ — match
    (λ q1 iq1 q2 iq2 h,
      feq2 (λ (a : τ B.prd) (b : τ B.prd), a B.∧ b)
        (ih1 q1 (split₁ (B.prd_eq p1 q1) (B.prd_eq p2 q2) h))
        (ih2 q2 (split₂ (B.prd_eq p1 q1) (B.prd_eq p2 q2) h)))
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// case p1 ∨ p2
symbol c_or (p1 : B.Prd) (ih1 : π (p0 p1)) (p2 : B.Prd) (ih2 : π (p0 p2))
  : π (p0 (p1 B.∨ p2)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq (p1 B.∨ p2) Q) ⇒ ((p1 B.∨ p2) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    // ∨ — match
    (λ q1 iq1 q2 iq2 h,
      feq2 (λ (a : τ B.prd) (b : τ B.prd), a B.∨ b)
        (ih1 q1 (split₁ (B.prd_eq p1 q1) (B.prd_eq p2 q2) h))
        (ih2 q2 (split₂ (B.prd_eq p1 q1) (B.prd_eq p2 q2) h)))
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// case p1 ⇒ p2
symbol c_imp (p1 : B.Prd) (ih1 : π (p0 p1)) (p2 : B.Prd) (ih2 : π (p0 p2))
  : π (p0 (p1 B.⇒ p2)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq (p1 B.⇒ p2) Q) ⇒ ((p1 B.⇒ p2) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    // ⇒ — match
    (λ q1 iq1 q2 iq2 h,
      feq2 (λ (a : τ B.prd) (b : τ B.prd), a B.⇒ b)
        (ih1 q1 (split₁ (B.prd_eq p1 q1) (B.prd_eq p2 q2) h))
        (ih2 q2 (split₂ (B.prd_eq p1 q1) (B.prd_eq p2 q2) h)))
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// case p1 ⇔ p2
symbol c_iff (p1 : B.Prd) (ih1 : π (p0 p1)) (p2 : B.Prd) (ih2 : π (p0 p2))
  : π (p0 (p1 B.⇔ p2)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq (p1 B.⇔ p2) Q) ⇒ ((p1 B.⇔ p2) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    // ⇔ — match
    (λ q1 iq1 q2 iq2 h,
      feq2 (λ (a : τ B.prd) (b : τ B.prd), a B.⇔ b)
        (ih1 q1 (split₁ (B.prd_eq p1 q1) (B.prd_eq p2 q2) h))
        (ih2 q2 (split₂ (B.prd_eq p1 q1) (B.prd_eq p2 q2) h)))
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// case e1 = e2 (binary Exp-Exp producing Prd)
symbol c_equal (e1 : B.Exp) (ihe1 : π (p2 e1)) (e2 : B.Exp) (ihe2 : π (p2 e2))
  : π (p0 ((B.=) e1 e2)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq ((B.=) e1 e2) Q) ⇒ (((B.=) e1 e2) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    // = — match
    (λ f1 if1 f2 if2 h,
      feq2 (λ (a : τ B.exp) (b : τ B.exp), (B.=) a b)
        (ihe1 f1 (split₁ (B.exp_eq e1 f1) (B.exp_eq e2 f2) h))
        (ihe2 f2 (split₂ (B.exp_eq e1 f1) (B.exp_eq e2 f2) h)))
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// case e1 ∈ e2
symbol c_in (e1 : B.Exp) (ihe1 : π (p2 e1)) (e2 : B.Exp) (ihe2 : π (p2 e2))
  : π (p0 ((B.∈) e1 e2)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq ((B.∈) e1 e2) Q) ⇒ (((B.∈) e1 e2) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    // ∈ — match
    (λ f1 if1 f2 if2 h,
      feq2 (λ (a : τ B.exp) (b : τ B.exp), (B.∈) a b)
        (ihe1 f1 (split₁ (B.exp_eq e1 f1) (B.exp_eq e2 f2) h))
        (ihe2 f2 (split₂ (B.exp_eq e1 f1) (B.exp_eq e2 f2) h)))
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x q iq h, ⊥ₑ h)
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// case ∀ x p (Var-Prd binder)
symbol c_all (x : B.Var) (p : B.Prd) (ihp : π (p0 p))
  : π (p0 (B.∀ x p)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq (B.∀ x p) Q) ⇒ ((B.∀ x p) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    // ∀ — match
    (λ y q iq h,
      feq2 (λ (a : τ B.var) (b : τ B.prd), B.∀ a b)
        (var_eq_sound x y (split₁ (B.var_eq x y) (B.prd_eq p q) h))
        (ihp q (split₂ (B.var_eq x y) (B.prd_eq p q) h)))
    (λ y q iq h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// case ∃ x p
symbol c_ex (x : B.Var) (p : B.Prd) (ihp : π (p0 p))
  : π (p0 (B.∃ x p)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq (B.∃ x p) Q) ⇒ ((B.∃ x p) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    // ∃ — match
    (λ y q iq h,
      feq2 (λ (a : τ B.var) (b : τ B.prd), B.∃ a b)
        (var_eq_sound x y (split₁ (B.var_eq x y) (B.prd_eq p q) h))
        (ihp q (split₂ (B.var_eq x y) (B.prd_eq p q) h)))
    (λ y q iq h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// case ♢ x p
symbol c_dia (x : B.Var) (p : B.Prd) (ihp : π (p0 p))
  : π (p0 (B.♢ x p)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq (B.♢ x p) Q) ⇒ ((B.♢ x p) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    // ♢ — match
    (λ y q iq h,
      feq2 (λ (a : τ B.var) (b : τ B.prd), B.♢ a b)
        (var_eq_sound x y (split₁ (B.var_eq x y) (B.prd_eq p q) h))
        (ihp q (split₂ (B.var_eq x y) (B.prd_eq p q) h)))
    (λ y q iq h, ⊥ₑ h)
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// case ♡ x p
symbol c_hrt (x : B.Var) (p : B.Prd) (ihp : π (p0 p))
  : π (p0 (B.♡ x p)) ≔
  λ Q, B.ind_Prd
    (λ Q, istrue (B.prd_eq (B.♡ x p) Q) ⇒ ((B.♡ x p) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    // ♡ — match
    (λ y q iq h,
      feq2 (λ (a : τ B.var) (b : τ B.prd), B.♡ a b)
        (var_eq_sound x y (split₁ (B.var_eq x y) (B.prd_eq p q) h))
        (ihp q (split₂ (B.var_eq x y) (B.prd_eq p q) h)))
    (λ x, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e ie, ⊤ᵢ) ⊤ᵢ (λ e ie, ⊤ᵢ) (λ x p ip, ⊤ᵢ)
    Q;

// ========== Exp constructors ==========

// case #var x
symbol c_var (x : B.Var) : π (p2 (B.#var x)) ≔
  λ F, B.ind_Exp
    (λ e, ⊤)
    (λ F, istrue (B.exp_eq (B.#var x) F) ⇒ ((B.#var x) = F))
    // Prd branches (motive ⊤)
    (λ q iq, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    // #var — match
    (λ y h, feq B.#var (var_eq_sound x y h))
    // ↦ — mismatch
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    // ×
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    // 𝒫
    (λ e ie h, ⊥ₑ h)
    // big
    (λ h, ⊥ₑ h)
    // choice
    (λ e ie h, ⊥ₑ h)
    // comp
    (λ y q iq h, ⊥ₑ h)
    F;

// case e1 ↦ e2 (binary Exp)
symbol c_mapsto (e1 : B.Exp) (ihe1 : π (p2 e1)) (e2 : B.Exp) (ihe2 : π (p2 e2))
  : π (p2 (e1 B.↦ e2)) ≔
  λ F, B.ind_Exp
    (λ e, ⊤)
    (λ F, istrue (B.exp_eq (e1 B.↦ e2) F) ⇒ ((e1 B.↦ e2) = F))
    (λ q iq, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    // #var — mismatch
    (λ y h, ⊥ₑ h)
    // ↦ — match
    (λ f1 if1 f2 if2 h,
      feq2 (λ (a : τ B.exp) (b : τ B.exp), a B.↦ b)
        (ihe1 f1 (split₁ (B.exp_eq e1 f1) (B.exp_eq e2 f2) h))
        (ihe2 f2 (split₂ (B.exp_eq e1 f1) (B.exp_eq e2 f2) h)))
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e ie h, ⊥ₑ h)
    (λ h, ⊥ₑ h)
    (λ e ie h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    F;

// case e1 × e2
symbol c_times (e1 : B.Exp) (ihe1 : π (p2 e1)) (e2 : B.Exp) (ihe2 : π (p2 e2))
  : π (p2 (e1 B.× e2)) ≔
  λ F, B.ind_Exp
    (λ e, ⊤)
    (λ F, istrue (B.exp_eq (e1 B.× e2) F) ⇒ ((e1 B.× e2) = F))
    (λ q iq, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ y h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    // × — match
    (λ f1 if1 f2 if2 h,
      feq2 (λ (a : τ B.exp) (b : τ B.exp), a B.× b)
        (ihe1 f1 (split₁ (B.exp_eq e1 f1) (B.exp_eq e2 f2) h))
        (ihe2 f2 (split₂ (B.exp_eq e1 f1) (B.exp_eq e2 f2) h)))
    (λ e ie h, ⊥ₑ h)
    (λ h, ⊥ₑ h)
    (λ e ie h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    F;

// case 𝒫 e (unary Exp)
symbol c_pow (e : B.Exp) (ihe : π (p2 e)) : π (p2 (B.𝒫 e)) ≔
  λ F, B.ind_Exp
    (λ e, ⊤)
    (λ F, istrue (B.exp_eq (B.𝒫 e) F) ⇒ ((B.𝒫 e) = F))
    (λ q iq, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ y h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    // 𝒫 — match
    (λ f if1 h,
      feq (λ (a : τ B.exp), B.𝒫 a) (ihe f h))
    (λ h, ⊥ₑ h)
    (λ e ie h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    F;

// case big (nullary Exp)
symbol c_big : π (p2 B.big) ≔
  λ F, B.ind_Exp
    (λ e, ⊤)
    (λ F, istrue (B.exp_eq B.big F) ⇒ (B.big = F))
    (λ q iq, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ y h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e ie h, ⊥ₑ h)
    // big — match
    (λ h, eq_refl B.big)
    (λ e ie h, ⊥ₑ h)
    (λ y q iq h, ⊥ₑ h)
    F;

// case choice e (unary Exp)
symbol c_choice (e : B.Exp) (ihe : π (p2 e)) : π (p2 (B.choice e)) ≔
  λ F, B.ind_Exp
    (λ e, ⊤)
    (λ F, istrue (B.exp_eq (B.choice e) F) ⇒ ((B.choice e) = F))
    (λ q iq, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ y h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e ie h, ⊥ₑ h)
    (λ h, ⊥ₑ h)
    // choice — match
    (λ f if1 h,
      feq (λ (a : τ B.exp), B.choice a) (ihe f h))
    (λ y q iq h, ⊥ₑ h)
    F;

// case comp x p (Var-Prd producing Exp)
symbol c_comp (x : B.Var) (p : B.Prd) (ihp : π (p0 p))
  : π (p2 (B.comp x p)) ≔
  λ F, B.ind_Exp
    (λ e, ⊤)
    (λ F, istrue (B.exp_eq (B.comp x p) F) ⇒ ((B.comp x p) = F))
    (λ q iq, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ q1 iq1 q2 iq2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ x q iq, ⊤ᵢ)
    (λ y h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ e ie h, ⊥ₑ h)
    (λ h, ⊥ₑ h)
    (λ e ie h, ⊥ₑ h)
    // comp — match
    (λ y q iq h,
      feq2 (λ (a : τ B.var) (b : τ B.prd), B.comp a b)
        (var_eq_sound x y (split₁ (B.var_eq x y) (B.prd_eq p q) h))
        (ihp q (split₂ (B.var_eq x y) (B.prd_eq p q) h)))
    F;

// ---- prd_eq_sound ----

opaque symbol prd_eq_sound (P Q : B.Prd)
  : π (istrue (B.prd_eq P Q)) → π (P = Q) ≔
begin
  assume P; refine B.ind_Prd p0 p2
    c_neg c_and c_or c_imp c_iff c_equal c_in
    c_all c_ex c_dia c_hrt
    c_var c_mapsto c_times c_pow c_big c_choice c_comp
    P
end;

// ---- exp_eq_sound ----

opaque symbol exp_eq_sound (E F : B.Exp)
  : π (istrue (B.exp_eq E F)) → π (E = F) ≔
begin
  assume E; refine B.ind_Exp p0 p2
    c_neg c_and c_or c_imp c_iff c_equal c_in
    c_all c_ex c_dia c_hrt
    c_var c_mapsto c_times c_pow c_big c_choice c_comp
    E
end;

// ---- semantic corollary ----

opaque symbol sat_eq (P Q : B.Prd) (μ : I.Val)
  (h : π (istrue (B.prd_eq P Q)))
  : π (I.sat μ P ⇔ I.sat μ Q) ≔
begin
  assume P Q μ h;
  rewrite prd_eq_sound P Q h; apply ⇔_refl
end;
