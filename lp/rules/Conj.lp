// Conjunction (§A.1) — shallow encoding
require open pp2lp.B;

// ---- Helper lemmas ----

opaque symbol lemma x y z
  : (π y → π x)
  → (π (x ⇒ z) → π (y ⇒ z)) ≔
begin
  assume x y z h0 h1 h2;
  refine h1 (h0 h2)
end;

opaque symbol ineq0_imp_+1 i
  : π (¬ (i = 0))
  → π (`∃ j, i = (j +1)) ≔
begin
  induction
    {assume h0; refine ⊥ₑ (=⇒ (¬=_idem nat 0) h0)}
    {assume i h0 h1; refine ∃ᵢ i _; simplify; reflexivity}
end;

opaque symbol conj_rem_nth c j
  : π (conj (rem_nth c j))
  → π (nth ⊤ c j)
  → π (conj c) ≔
begin
  induction {
    simplify;
    assume j h0 h1;
    refine h1
  } {
    assume x c h0 i h1 h2;
    refine conj_sound x c _;
    refine ∧ᵢ _ _ {
      refine ∨ₑ (em (i = 0)) _ _ {
        assume h3;
        have H0: π ((nth ⊤ (x ∷ c) i) ⇒ x) {
          rewrite h3;
          simplify;
          assume h4;
          refine h4
        };
        refine H0 h2
      } {
        assume h3;
        have H0: π ((conj (rem_nth (x ∷ c) i)) ⇒ x) {
          refine ∃ₑ (ineq0_imp_+1 i h3) _;
          assume j h4; rewrite h4;
          assume h5;
          refine conj_head x (rem_nth c j) h5};
          refine H0 h1
      }
    } {
      refine ∨ₑ (em (i = 0)) _ _ {
        assume h3;
        have h1_imp_c : π ((conj (rem_nth (x ∷ c) i)) ⇒ (conj c)) {
          rewrite h3; simplify; assume h4; refine h4
        };
        refine h1_imp_c h1
      } {
        assume h3;
        refine ∃ₑ (ineq0_imp_+1 i h3) _;
        assume j h4;
        have H0 : π ((conj (rem_nth (x ∷ c) i)) ⇒ conj (rem_nth c j)) {
          rewrite h4; simplify;
          assume h5; refine conj_tail x (rem_nth c j) h5
        };
        have H1: π ((nth ⊤ (x ∷ c) i) ⇒ (nth ⊤ c j)) {
          rewrite h4; simplify;
          assume h5; refine h5
        };
        refine h0 j (H0 h1) (H1 h2)
      }
    }
  }
end;

opaque symbol conj_cat c0 c1
  : π (conj (c0 ++ c1))
  → π (conj c0 ∧ conj c1) ≔
begin
  induction
    {assume c h0; refine ∧ᵢ ⊤ᵢ h0}
    {assume x0 c h0 c1 h1;
    have H0: π ((conj ((x0 ∷ c) ++ c1)) ⇒ (x0 ∧ conj (c ++ c1)))
      {rewrite cat_cons; assume h2;
      refine conj_correct x0 (c ++ c1) h2};
    have H1: π (conj c ∧ conj c1) {refine (h0 c1 (∧ₑ₂ (H0 h1)))};
    refine ∧ᵢ _ _
      {refine conj_sound x0 c _;
      refine ∧ᵢ _ _
        {refine (∧ₑ₁ (H0 h1))}
        {refine ∧ₑ₁ H1}}
      {refine ∧ₑ₂ H1}}
end;

// ---- Base rules ----

// AND1: H ⊢ ¬Q ⇒ R; H ⊢ ¬P ⇒ R → H ⊢ ¬(P ∧ Q) ⇒ R
opaque symbol AND1 [P Q R]
  : π (¬ Q ⇒ R)
  → π (¬ P ⇒ R)
  → π (¬ (P ∧ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2 h3;
  have h : π (¬ P ∨ ¬ Q)
    { refine =⇒ (deMorgan_∧ P Q) h3 };
  refine ∨ₑ h _ _
    { assume hnp; refine h2 hnp }
    { assume hnq; refine h1 hnq }
end;

// AND2: H ⊢ P ⇒ ¬Q → H ⊢ ¬(P ∧ Q)
opaque symbol AND2 [P Q]
  : π (P ⇒ ¬ Q)
  → π (¬ (P ∧ Q)) ≔
begin
  assume P Q h1 h2;
  refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2)
end;

// AND3: H ⊢ P ⇒ (Q ⇒ R) → H ⊢ (P ∧ Q) ⇒ R
opaque symbol AND3 [P Q R]
  : π (P ⇒ Q ⇒ R)
  → π ((P ∧ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2;
  refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2)
end;

// AND4: H ⊢ Q; H ⊢ P → H ⊢ P ∧ Q
opaque symbol AND4 [P Q]
  : π Q
  → π P
  → π (P ∧ Q) ≔
begin
  assume P Q h1 h2;
  refine ∧ᵢ h2 h1
end;

// Helper: extract i-th element from conjunction.
opaque symbol conj_nth (c : 𝕃 o) (i : ℕ)
  : π (conj c)
  → π (nth ⊤ c i) ≔
begin
  induction {
    simplify; assume i h; refine ⊤ᵢ
  } {
    assume x c' IH;
    induction {
      assume h; simplify; refine conj_head x c' h
    } {
      assume n IHn h; simplify;
      refine IH n (conj_tail x c' h)
    }
  }
end;

// Helper: combine two conjunctions.
opaque symbol conj_app (c0 c1 : 𝕃 o)
  : π (conj c0)
  → π (conj c1)
  → π (conj (c0 ++ c1)) ≔
begin
  induction {
    simplify; assume c1 h0 h1; refine h1
  } {
    assume x c0' IH c1 h0 h1;
    rewrite cat_cons;
    refine conj_sound x (c0' ++ c1) _;
    refine ∧ᵢ (conj_head x c0' h0) (IH c1 (conj_tail x c0' h0) h1)
  }
end;

// Helper: dropping a conjunct preserves the rest.
opaque symbol conj_drop (c : 𝕃 o) (j : ℕ)
  : π (conj c)
  → π (conj (rem_nth c j)) ≔
begin
  induction {
    simplify; assume j h; refine ⊤ᵢ
  } {
    assume x c' IH;
    induction {
      assume h; simplify; refine conj_tail x c' h
    } {
      assume n IHn h; simplify;
      refine conj_sound x (rem_nth c' n) _;
      refine ∧ᵢ (conj_head x c' h) (IH n (conj_tail x c' h))
    }
  }
end;

// AND5: P ∧ ··· contains A at i and (A ⇒ B) at j; remove (A ⇒ B), append B.
// H ⊢ conj(rem_nth c j ++ [B]) ⇒ R → H ⊢ conj c ⇒ R
symbol AND5 [r : Prop] (c : 𝕃 o) (a b : Prop) (i j : ℕ)
  : π ((nth ⊤ c i) = a)
  → π ((nth ⊤ c j) = (a ⇒ b))
  → π ((conj (rem_nth c j ++ (b ∷ □))) ⇒ r)
  → π ((conj c) ⇒ r) ≔
begin
  assume r c a b i j h0 h1 hsub hc;
  have ha : π a { rewrite left h0; refine conj_nth c i hc };
  have hab : π (a ⇒ b) { rewrite left h1; refine conj_nth c j hc };
  have hb : π b { refine hab ha };
  have hrem : π (conj (rem_nth c j)) { refine conj_drop c j hc };
  refine hsub (conj_app (rem_nth c j) (b ∷ □) hrem
    (conj_sound b □ (∧ᵢ hb ⊤ᵢ)))
end;

// ---- Primed variants (equality-based) ----

// AND1_1: multi-premise, rewrites ¬(P∧Q)⇒R = (¬Q⇒R) ∧ (¬P⇒R).
opaque symbol AND1_1 [P Q R S1 S2 : Prop]
  : π ((¬ Q ⇒ R) = S1)
  → π ((¬ P ⇒ R) = S2)
  → π ((¬ (P ∧ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin
  assume P Q R S1 S2 h1 h2;
  have eq : π ((¬ (P ∧ Q) ⇒ R) = ((¬ Q ⇒ R) ∧ (¬ P ⇒ R)))
    { refine propExt _ _ _ _
      { assume h; refine ∧ᵢ
        (λ hnq, h (λ hpq, hnq (∧ₑ₂ hpq)))
        (λ hnp, h (λ hpq, hnp (∧ₑ₁ hpq))) }
      { assume h hnpq;
        have hnpnq : π (¬ P ∨ ¬ Q) { refine =⇒ (deMorgan_∧ P Q) hnpq };
        refine ∨ₑ hnpnq _ _
        { assume hnp; refine ∧ₑ₂ h hnp }
        { assume hnq; refine ∧ₑ₁ h hnq } } };
  rewrite eq; rewrite h1; rewrite h2; reflexivity
end;

// AND2_1: pass-through. ¬(P∧Q) = (P ⇒ ¬Q).
opaque symbol AND2_1 [P Q S : Prop]
  : π ((P ⇒ ¬ Q) = S)
  → π (¬ (P ∧ Q) = S) ≔
begin
  assume P Q S h;
  have eq : π (¬ (P ∧ Q) = (P ⇒ ¬ Q))
    { refine propExt _ _ _ _
      { assume h1 hp hq; refine h1 (∧ᵢ hp hq) }
      { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) } };
  rewrite eq; refine h
end;

// AND3_1: pass-through. (P∧Q)⇒R = P⇒Q⇒R.
opaque symbol AND3_1 [P Q R S : Prop]
  : π ((P ⇒ Q ⇒ R) = S)
  → π (((P ∧ Q) ⇒ R) = S) ≔
begin
  assume P Q R S h;
  have eq : π (((P ∧ Q) ⇒ R) = (P ⇒ Q ⇒ R))
    { refine propExt _ _ _ _
      { assume h1 hp hq; refine h1 (∧ᵢ hp hq) }
      { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) } };
  rewrite eq; refine h
end;

// AND4_1: multi-premise. P∧Q = S1 ∧ S2 (rewrites under ∧).
opaque symbol AND4_1 [P Q S1 S2 : Prop]
  : π (Q = S1)
  → π (P = S2)
  → π ((P ∧ Q) = (S1 ∧ S2)) ≔
begin
  assume P Q S1 S2 h1 h2;
  rewrite ∧_com; rewrite h1; rewrite h2; reflexivity
end;

// Helper: nth after set_nth at same index gives new value.
// AND5_1: equality-based. (conj c ⇒ r) = (conj(rem_nth c j ++ [b]) ⇒ r).
opaque symbol AND5_1 [r s : Prop] (c : 𝕃 o) (a b : Prop) (i j : ℕ)
  : π ((nth ⊤ c i) = a)
  → π ((nth ⊤ c j) = (a ⇒ b))
  → π (((conj (rem_nth c j ++ (b ∷ □))) ⇒ r) = s)
  → π (((conj c) ⇒ r) = s) ≔
begin
  assume r s c a b i j h0 h1 heq;
  have fwd : π (conj c) → π (conj (rem_nth c j ++ (b ∷ □)))
    { assume hc;
      have ha : π a { refine =⇒ h0 (conj_nth c i hc) };
      have hab : π (a ⇒ b) { refine =⇒ h1 (conj_nth c j hc) };
      have hb : π b { refine hab ha };
      have hremj : π (conj (rem_nth c j)) { refine conj_drop c j hc };
      refine conj_app (rem_nth c j) (b ∷ □) hremj
        (conj_sound b □ (∧ᵢ hb ⊤ᵢ)) };
  have bwd : π (conj (rem_nth c j ++ (b ∷ □))) → π (conj c)
    { assume hremb;
      have hrem : π (conj (rem_nth c j))
        { refine ∧ₑ₁ (conj_cat (rem_nth c j) (b ∷ □) hremb) };
      have hb : π b
        { refine conj_head b □ (∧ₑ₂ (conj_cat (rem_nth c j) (b ∷ □) hremb)) };
      have hab : π (a ⇒ b) { assume ha; refine hb };
      have hnthj : π (nth ⊤ c j) { rewrite h1; refine hab };
      refine conj_rem_nth c j hrem hnthj };
  have eq : π ((conj c ⇒ r) = (conj (rem_nth c j ++ (b ∷ □)) ⇒ r))
    { refine propExt _ _ _ _
      { assume hcr hremb; refine hcr (bwd hremb) }
      { assume hremr hc; refine hremr (fwd hc) } };
  rewrite eq; refine heq
end;
