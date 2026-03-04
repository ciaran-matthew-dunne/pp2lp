// Normalisation rules (spec §A.12)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ---- first → second normalisation ----------------
// NRM1: x not free in P; H ⊢ P ⇒ S  ⟹  H ⊢ (♢x · P) ⇒ S
symbol NRM1 [H x P S]
  : ⁇ (pnf x P) → (H ⊩ P ⇒ S) → (H ⊩ (♢ x P) ⇒ S);

// NRM2: x not free in P; H ⊢ (P ⇒ ♢x · Q) ⇒ S  ⟹  H ⊢ ♢x · (P ⇒ Q) ⇒ S
symbol NRM2 [H x P Q S]
  : ⁇ (pnf x P) → (H ⊩ (P ⇒ ♢ x Q) ⇒ S) → (H ⊩ (♢ x (P ⇒ Q)) ⇒ S);

// NRM3: x not free in Q; Q ≠ FALSE; H ⊢ (Q ⇒ S) ∧ ((∀x · ¬P) ⇒ S)
//   ⟹  H ⊢ ♢x · (P ⇒ Q) ⇒ S
symbol NRM3 [H x P Q S]
  : ⁇ (pnf x Q) → (H ⊩ (Q ⇒ S) ∧ ((∀ x (¬ P)) ⇒ S))
  → (H ⊩ (♢ x (P ⇒ Q)) ⇒ S);

// NRM4: x not free in Q; H ⊢ (Q ⇒ ♢x · (P ⇒ R)) ⇒ S
//   ⟹  H ⊢ ♢x · (P ⇒ (Q ⇒ R)) ⇒ S
symbol NRM4 [H x P Q R S]
  : ⁇ (pnf x Q) → (H ⊩ (Q ⇒ ♢ x (P ⇒ R)) ⇒ S)
  → (H ⊩ (♢ x (P ⇒ (Q ⇒ R))) ⇒ S);

// NRM5: H ⊢ ♢x · (P ∧ Q ⇒ R) ⇒ S  ⟹  H ⊢ ♢x · (P ⇒ (Q ⇒ R)) ⇒ S
symbol NRM5 [H x P Q R S]
  : (H ⊩ (♢ x (P ∧ Q ⇒ R)) ⇒ S) → (H ⊩ (♢ x (P ⇒ (Q ⇒ R))) ⇒ S);

// NRM6: H ⊢ ♢x · (R ⇒ P) ⇒ (♢x · (R ⇒ Q) ⇒ S)
//   ⟹  H ⊢ ♢x · (R ⇒ P ∧ Q) ⇒ S
symbol NRM6 [H x P Q R S]
  : (H ⊩ (♢ x (R ⇒ P)) ⇒ ((♢ x (R ⇒ Q)) ⇒ S))
  → (H ⊩ (♢ x (R ⇒ P ∧ Q)) ⇒ S);

// NRM7: H ⊢ (♢x · P) ⇒ ((♢x · Q) ⇒ S)  ⟹  H ⊢ ♢x · (P ∧ Q) ⇒ S
symbol NRM7 [H x P Q S]
  : (H ⊩ (♢ x P) ⇒ ((♢ x Q) ⇒ S))
  → (H ⊩ (♢ x (P ∧ Q)) ⇒ S);

// NRM8: suppress quantifications under ♢.
// Case 1: x, y distinct.
symbol NRM8 [H x y Q S]
  : ⁇ (nf y (#prd (♢ x (∀ y Q))))  // x, y distinct
  → (H ⊩ (♢ (x ⨾ y) Q) ⇒ S) → (H ⊩ (♢ x (∀ y Q)) ⇒ S);

// Case 2: x, y not distinct; z fresh; K = [y := z] Q.
symbol NRM8f [H x y z] [Q K : Prd] [S]
  : ⁇ (psub y (#var z) Q == K)
  → (H ⊩ (♢ (x ⨾ z) K) ⇒ S) → (H ⊩ (♢ x (∀ y Q)) ⇒ S);

// NRM9: suppress quantifications in implication under ♢.
// Case 1: x, y distinct; y not free in P.
symbol NRM9 [H x y P Q S]
  : ⁇ (nf y (#prd (♢ x (P ⇒ ∀ y Q))))  // x, y distinct
  → ⁇ (pnf y P)                          // y not free in P
  → (H ⊩ (♢ (x ⨾ y) (P ⇒ Q)) ⇒ S)
  → (H ⊩ (♢ x (P ⇒ ∀ y Q)) ⇒ S);

// Case 2: x, y not distinct or y free in P; z fresh; K = [y := z] Q.
symbol NRM9f [H x y z P] [Q K : Prd] [S]
  : ⁇ (pnf z P and pnf z Q)  // z fresh
  → ⁇ (psub y (#var z) Q == K)
  → (H ⊩ (♢ (x ⨾ z) (P ⇒ K)) ⇒ S)
  → (H ⊩ (♢ x (P ⇒ ∀ y Q)) ⇒ S);

// ---- second → third normalisation ----------------
// NRM10: H ⊢ ♡x · ¬(P ∧ Q) ⇒ R  ⟹  H ⊢ ♢x · (P ∧ Q ⇒ FALSE) ⇒ R
symbol NRM10 [H x P Q R]
  : (H ⊩ (♡ x (¬ (P ∧ Q))) ⇒ R)
  → (H ⊩ (♢ x ((P ∧ Q) ⇒ FALSE)) ⇒ R);

// NRM11: H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ R  ⟹  H ⊢ ♢x · (P ⇒ FALSE) ⇒ R
symbol NRM11 [H x P R]
  : (H ⊩ (♡ x (¬ (TRUE ∧ P))) ⇒ R)
  → (H ⊩ (♢ x (P ⇒ FALSE)) ⇒ R);

// NRM12: H ⊢ ♡x · ¬(P ∧ Q) ⇒ R  ⟹  H ⊢ ♢x · (P ⇒ ¬Q) ⇒ R
symbol NRM12 [H x P Q R]
  : (H ⊩ (♡ x (¬ (P ∧ Q))) ⇒ R)
  → (H ⊩ (♢ x (P ⇒ ¬ Q)) ⇒ R);

// NRM13: H ⊢ ♡x · ¬(P ∧ ¬Q) ⇒ R  ⟹  H ⊢ ♢x · (P ⇒ Q) ⇒ R
symbol NRM13 [H x P Q R]
  : (H ⊩ (♡ x (¬ (P ∧ ¬ Q))) ⇒ R)
  → (H ⊩ (♢ x (P ⇒ Q)) ⇒ R);

// NRM14: H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ R  ⟹  H ⊢ (♢x · ¬P) ⇒ R
symbol NRM14 [H x P R]
  : (H ⊩ (♡ x (¬ (TRUE ∧ P))) ⇒ R)
  → (H ⊩ (♢ x (¬ P)) ⇒ R);

// NRM15: H ⊢ ♡x · ¬(TRUE ∧ ¬P) ⇒ R  ⟹  H ⊢ (♢x · P) ⇒ R
symbol NRM15 [H x P R]
  : (H ⊩ (♡ x (¬ (TRUE ∧ ¬ P))) ⇒ R)
  → (H ⊩ (♢ x P) ⇒ R);

// NRM16: ∀x · P is in H  ⟹  H ⊢ (♡x · P) ⇒ Q
symbol NRM16 [H x P Q]
  : ⁇ (∀ x P dans H) → (H ⊩ (♡ x P) ⇒ Q);

// ---- contradictions on hypothesis promotion ----------------
// NRM17: ∀x · ¬(TRUE ∧ P) is in H; ∃E. [x := E] P = R
//   ⟹  H ⊢ ♡y · ¬(TRUE ∧ ¬R) ⇒ Q
symbol NRM17 [H x y P R Q]
  : ⁇ (∀ x (¬ (TRUE ∧ P)) dans H)
  → (H ⊩ (♡ y (¬ (TRUE ∧ ¬ R))) ⇒ Q);

// NRM18: ∀x · ¬(TRUE ∧ ¬P) is in H; ∃E. [x := E] P = R
//   ⟹  H ⊢ ♡y · ¬(TRUE ∧ R) ⇒ Q
symbol NRM18 [H x y P R Q]
  : ⁇ (∀ x (¬ (TRUE ∧ ¬ P)) dans H)
  → (H ⊩ (♡ y (¬ (TRUE ∧ R))) ⇒ Q);

// NRM19: P is in H; ∃E. [x := E] R = P  ⟹  H ⊢ ♡x · ¬(TRUE ∧ R) ⇒ Q
symbol NRM19 [H x P R Q]
  : ⁇ (P dans H)
  → (H ⊩ (♡ x (¬ (TRUE ∧ R))) ⇒ Q);

// ---- one-point rules (NRM20–NRM24) ----------------
// NRM20: x not free in E; H ⊢ ♡y · ¬[x := E]P ⇒ Q
//   ⟹  H ⊢ ♡(x,y) · ¬(P ∧ x = E) ⇒ Q
symbol NRM20 [H x y E P Q]
  : ⁇ (enf x E)
  → (H ⊩ (♡ y (¬ (psub x E P))) ⇒ Q)
  → (H ⊩ (♡ (x ⨾ y) (¬ (P ∧ (#var x = E)))) ⇒ Q);

// NRM21: x not free in E; H ⊢ ♡y · ¬[x := E]P ⇒ Q
//   ⟹  H ⊢ ♡(x,y) · ¬(P ∧ E = x) ⇒ Q
symbol NRM21 [H x y E P Q]
  : ⁇ (enf x E)
  → (H ⊩ (♡ y (¬ (psub x E P))) ⇒ Q)
  → (H ⊩ (♡ (x ⨾ y) (¬ (P ∧ (E = #var x)))) ⇒ Q);

// NRM22: x not free in E; H ⊢ ¬[x := E]P ⇒ Q
//   ⟹  H ⊢ ♡x · ¬(P ∧ x = E) ⇒ Q
symbol NRM22 [H x E P Q]
  : ⁇ (enf x E)
  → (H ⊩ ¬ (psub x E P) ⇒ Q)
  → (H ⊩ (♡ x (¬ (P ∧ (#var x = E)))) ⇒ Q);

// NRM23: x not free in E; H ⊢ ¬[x := E]P ⇒ Q
//   ⟹  H ⊢ ♡x · ¬(P ∧ E = x) ⇒ Q
symbol NRM23 [H x E P Q]
  : ⁇ (enf x E)
  → (H ⊩ ¬ (psub x E P) ⇒ Q)
  → (H ⊩ (♡ x (¬ (P ∧ (E = #var x)))) ⇒ Q);

// NRM24: P is not of the form A ∧ B;
//   H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ Q  ⟹  H ⊢ ♡x · ¬P ⇒ Q
symbol NRM24 [H x P Q]
  : (H ⊩ (♡ x (¬ (TRUE ∧ P))) ⇒ Q)
  → (H ⊩ (♡ x (¬ P)) ⇒ Q);

// NRM25: x not free in P; H ⊢ P  ⟹  H ⊢ ♡(x) · P
symbol NRM25 [H x P]
  : ⁇ (pnf x P) → (H ⊩ P) → (H ⊩ ♡ x P);

// NRM26: y not free in P; H ⊢ ♡(x,...) · P  ⟹  H ⊢ ♡(x,y,...) · P
symbol NRM26 [H x y P]
  : ⁇ (pnf y P) → (H ⊩ ♡ x P) → (H ⊩ ♡ (x ⨾ y) P);

// NRM27–NRM30: arithmetic normalisation (use of solver to eliminate variables).
symbol NRM27 [H xs P R]
  : (H ⊩ R) → (H ⊩ ♡ xs P);

symbol NRM28 [H x P S R]
  : (H ⊩ ¬ S ⇒ R) → (H ⊩ (♡ x (¬ P)) ⇒ R);

symbol NRM29 [H xs P S R]
  : (H ⊩ S ⇒ R) → (H ⊩ (♡ xs (¬ P)) ⇒ R);

symbol NRM29_1 [H xs P S R]
  : (H ⊩ S ⇒ R) → (H ⊩ (♡ xs (¬ P)) ⇒ R);

symbol NRM30 [H x P S R]
  : (H ⊩ ¬ S ⇒ R) → (H ⊩ (♡ x (¬ P)) ⇒ R);

symbol NRM30_1 [H x P S R]
  : (H ⊩ ¬ S ⇒ R) → (H ⊩ (♡ x (¬ P)) ⇒ R);

// ---- primed (result-producing) variants ----------------

// NRM1': Schema 1.
symbol NRM1' [H x P S]
  : ⁇ (pnf x P)
  → Res (H ⟝ P ⇒ S) → Res (H ⟝ (♢ x P) ⇒ S)
≔ λ _ ρ, result (obtain ρ);

symbol NRM2' [H x P Q S]
  : ⁇ (pnf x P) → Res (H ⟝ (P ⇒ ♢ x Q) ⇒ S) → Res (H ⟝ (♢ x (P ⇒ Q)) ⇒ S)
≔ λ _ ρ, result (obtain ρ);

symbol NRM3' [H x P Q S]
  : ⁇ (pnf x Q) → Res (H ⟝ (Q ⇒ S) ∧ ((∀ x (¬ P)) ⇒ S))
  → Res (H ⟝ (♢ x (P ⇒ Q)) ⇒ S)
≔ λ _ ρ, result (obtain ρ);

symbol NRM4' [H x P Q R S]
  : ⁇ (pnf x Q) → Res (H ⟝ (Q ⇒ ♢ x (P ⇒ R)) ⇒ S)
  → Res (H ⟝ (♢ x (P ⇒ (Q ⇒ R))) ⇒ S)
≔ λ _ ρ, result (obtain ρ);

symbol NRM5' [H x P Q R S]
  : Res (H ⟝ (♢ x (P ∧ Q ⇒ R)) ⇒ S) → Res (H ⟝ (♢ x (P ⇒ (Q ⇒ R))) ⇒ S)
≔ λ ρ, result (obtain ρ);

symbol NRM6' [H x P Q R S]
  : Res (H ⟝ (♢ x (R ⇒ P)) ⇒ ((♢ x (R ⇒ Q)) ⇒ S))
  → Res (H ⟝ (♢ x (R ⇒ P ∧ Q)) ⇒ S)
≔ λ ρ, result (obtain ρ);

symbol NRM7' [H x P Q S]
  : Res (H ⟝ (♢ x P) ⇒ ((♢ x Q) ⇒ S))
  → Res (H ⟝ (♢ x (P ∧ Q)) ⇒ S)
≔ λ ρ, result (obtain ρ);

symbol NRM8' [H x y Q S]
  : ⁇ (nf y (#prd (♢ x (∀ y Q))))
  → Res (H ⟝ (♢ (x ⨾ y) Q) ⇒ S) → Res (H ⟝ (♢ x (∀ y Q)) ⇒ S)
≔ λ _ ρ, result (obtain ρ);

symbol NRM8f' [H x y z] [Q K : Prd] [S]
  : ⁇ (psub y (#var z) Q == K)
  → Res (H ⟝ (♢ (x ⨾ z) K) ⇒ S) → Res (H ⟝ (♢ x (∀ y Q)) ⇒ S)
≔ λ _ ρ, result (obtain ρ);

symbol NRM9' [H x y P Q S]
  : ⁇ (nf y (#prd (♢ x (P ⇒ ∀ y Q))))
  → ⁇ (pnf y P)
  → Res (H ⟝ (♢ (x ⨾ y) (P ⇒ Q)) ⇒ S)
  → Res (H ⟝ (♢ x (P ⇒ ∀ y Q)) ⇒ S)
≔ λ _ _ ρ, result (obtain ρ);

symbol NRM9f' [H x y z P] [Q K : Prd] [S]
  : ⁇ (pnf z P and pnf z Q)
  → ⁇ (psub y (#var z) Q == K)
  → Res (H ⟝ (♢ (x ⨾ z) (P ⇒ K)) ⇒ S)
  → Res (H ⟝ (♢ x (P ⇒ ∀ y Q)) ⇒ S)
≔ λ _ _ ρ, result (obtain ρ);

symbol NRM10' [H x P Q R]
  : Res (H ⟝ (♡ x (¬ (P ∧ Q))) ⇒ R) → Res (H ⟝ (♢ x ((P ∧ Q) ⇒ FALSE)) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol NRM11' [H x P R]
  : Res (H ⟝ (♡ x (¬ (TRUE ∧ P))) ⇒ R) → Res (H ⟝ (♢ x (P ⇒ FALSE)) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol NRM12' [H x P Q R]
  : Res (H ⟝ (♡ x (¬ (P ∧ Q))) ⇒ R) → Res (H ⟝ (♢ x (P ⇒ ¬ Q)) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol NRM13' [H x P Q R]
  : Res (H ⟝ (♡ x (¬ (P ∧ ¬ Q))) ⇒ R) → Res (H ⟝ (♢ x (P ⇒ Q)) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol NRM14' [H x P R]
  : Res (H ⟝ (♡ x (¬ (TRUE ∧ P))) ⇒ R) → Res (H ⟝ (♢ x (¬ P)) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol NRM15' [H x P R]
  : Res (H ⟝ (♡ x (¬ (TRUE ∧ ¬ P))) ⇒ R) → Res (H ⟝ (♢ x P) ⇒ R)
≔ λ ρ, result (obtain ρ);

// NRM16': Schema 0.
symbol NRM16' [H x P Q]
  : ⁇ (∀ x P dans H) → Res (H ⟝ (♡ x P) ⇒ Q)
≔ λ _, result TRUE;

// NRM17': Schema 0.
symbol NRM17' [H x y P R Q]
  : ⁇ (∀ x (¬ (TRUE ∧ P)) dans H)
  → Res (H ⟝ (♡ y (¬ (TRUE ∧ ¬ R))) ⇒ Q)
≔ λ _, result TRUE;

// NRM18': Schema 0.
symbol NRM18' [H x y P R Q]
  : ⁇ (∀ x (¬ (TRUE ∧ ¬ P)) dans H)
  → Res (H ⟝ (♡ y (¬ (TRUE ∧ R))) ⇒ Q)
≔ λ _, result TRUE;

// NRM19': Schema 0.
symbol NRM19' [H x P R Q]
  : ⁇ (P dans H)
  → Res (H ⟝ (♡ x (¬ (TRUE ∧ R))) ⇒ Q)
≔ λ _, result TRUE;

// NRM20': Schema 1.
symbol NRM20' [H x y E P Q]
  : ⁇ (enf x E)
  → Res (H ⟝ (♡ y (¬ (psub x E P))) ⇒ Q)
  → Res (H ⟝ (♡ (x ⨾ y) (¬ (P ∧ (#var x = E)))) ⇒ Q)
≔ λ _ ρ, result (obtain ρ);

// NRM21': Schema 1.
symbol NRM21' [H x y E P Q]
  : ⁇ (enf x E)
  → Res (H ⟝ (♡ y (¬ (psub x E P))) ⇒ Q)
  → Res (H ⟝ (♡ (x ⨾ y) (¬ (P ∧ (E = #var x)))) ⇒ Q)
≔ λ _ ρ, result (obtain ρ);

// NRM22': Schema 1.
symbol NRM22' [H x E P Q]
  : ⁇ (enf x E)
  → Res (H ⟝ ¬ (psub x E P) ⇒ Q)
  → Res (H ⟝ (♡ x (¬ (P ∧ (#var x = E)))) ⇒ Q)
≔ λ _ ρ, result (obtain ρ);

// NRM23': Schema 1.
symbol NRM23' [H x E P Q]
  : ⁇ (enf x E)
  → Res (H ⟝ ¬ (psub x E P) ⇒ Q)
  → Res (H ⟝ (♡ x (¬ (P ∧ (E = #var x)))) ⇒ Q)
≔ λ _ ρ, result (obtain ρ);

// NRM24': Schema 1.
symbol NRM24' [H x P Q]
  : Res (H ⟝ (♡ x (¬ (TRUE ∧ P))) ⇒ Q)
  → Res (H ⟝ (♡ x (¬ P)) ⇒ Q)
≔ λ ρ, result (obtain ρ);

// NRM25': Schema 1.
symbol NRM25' [H x P]
  : ⁇ (pnf x P) → Res (H ⟝ P) → Res (H ⟝ ♡ x P)
≔ λ _ ρ, result (obtain ρ);

// NRM26': Schema 1.
symbol NRM26' [H x y P]
  : ⁇ (pnf y P) → Res (H ⟝ ♡ x P) → Res (H ⟝ ♡ (x ⨾ y) P)
≔ λ _ ρ, result (obtain ρ);

// NRM27': Schema 1.
symbol NRM27' [H xs P R]
  : Res (H ⟝ R) → Res (H ⟝ ♡ xs P)
≔ λ ρ, result (obtain ρ);

// NRM28': Schema 1.
symbol NRM28' [H x P S R]
  : Res (H ⟝ ¬ S ⇒ R) → Res (H ⟝ (♡ x (¬ P)) ⇒ R)
≔ λ ρ, result (obtain ρ);

// NRM29': Schema 1.
symbol NRM29' [H xs P S R]
  : Res (H ⟝ S ⇒ R) → Res (H ⟝ (♡ xs (¬ P)) ⇒ R)
≔ λ ρ, result (obtain ρ);

// NRM29_1': Schema 1.
symbol NRM29_1' [H xs P S R]
  : Res (H ⟝ S ⇒ R) → Res (H ⟝ (♡ xs (¬ P)) ⇒ R)
≔ λ ρ, result (obtain ρ);

// NRM30': Schema 1.
symbol NRM30' [H x P S R]
  : Res (H ⟝ ¬ S ⇒ R) → Res (H ⟝ (♡ x (¬ P)) ⇒ R)
≔ λ ρ, result (obtain ρ);

// NRM30_1': Schema 1.
symbol NRM30_1' [H x P S R]
  : Res (H ⟝ ¬ S ⇒ R) → Res (H ⟝ (♡ x (¬ P)) ⇒ R)
≔ λ ρ, result (obtain ρ);
