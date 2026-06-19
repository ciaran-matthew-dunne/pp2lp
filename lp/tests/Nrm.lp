// Tests for rules/Nrm.lp (normalisation under ♢ / ♡, tuple-indexed).
require open pp2lp.Prelude;

// ---- NRM1-7: logical transformations under ♢ ----
symbol t_NRM1 (n : ℕ) (P S : Prop) (h : π (P ⇒ S))
  : π ((`♢ _ : Tuple n, P) ⇒ S) ≔ NRM1 h;
symbol t_NRM2 (n : ℕ) (P : Prop) (Q : Tuple n → Prop) (S : Prop)
  (h : π ((P ⇒ (`♢ v, Q v)) ⇒ S)) : π ((`♢ v, P ⇒ Q v) ⇒ S) ≔ NRM2 h;
symbol t_NRM3 (n : ℕ) (P : Tuple n → Prop) (Q S : Prop)
  (h : π (⋀_snoc (Q ⇒ S) ((`!! v, ¬ (P v)) ⇒ S))) : π ((`♢ v, P v ⇒ Q) ⇒ S) ≔ NRM3 h;
symbol t_NRM4 (n : ℕ) (P R : Tuple n → Prop) (Q S : Prop)
  (h : π ((Q ⇒ (`♢ v, P v ⇒ R v)) ⇒ S)) : π ((`♢ v, P v ⇒ Q ⇒ R v) ⇒ S) ≔ NRM4 h;
symbol t_NRM5 (n : ℕ) (P Q R : Tuple n → Prop) (S : Prop)
  (h : π ((`♢ v, ⋀_snoc (P v) (Q v) ⇒ R v) ⇒ S)) : π ((`♢ v, P v ⇒ Q v ⇒ R v) ⇒ S) ≔ NRM5 h;
symbol t_NRM6 (n : ℕ) (Qs : Tuple n → 𝕃* o) (P R : Tuple n → Prop) (S : Prop)
  (h : π ((`♢ v, R v ⇒ ⋀ (Qs v)) ⇒ ((`♢ v, R v ⇒ P v) ⇒ S)))
  : π ((`♢ v, R v ⇒ ⋀ (Qs v ∷ P v)) ⇒ S) ≔ NRM6 h;
symbol t_NRM7 (n : ℕ) (Qs : Tuple n → 𝕃* o) (P : Tuple n → Prop) (S : Prop)
  (h : π ((`♢ v, ⋀ (Qs v)) ⇒ ((`♢ v, P v) ⇒ S)))
  : π ((`♢ v : Tuple n, ⋀ (Qs v ∷ P v)) ⇒ S) ≔ NRM7 h;

// ---- NRM8-9: compound ↔ mixed binders ----
symbol t_NRM8 (n m : ℕ) (Q : Tuple n → Tuple m → Prop) (S : Prop)
  (h : π ((`♢ v : Tuple (n ++ m), Q (take [n] [m] v) (drop [n] [m] v)) ⇒ S))
  : π ((`♢ x : Tuple n, `!! y : Tuple m, Q x y) ⇒ S) ≔ NRM8 h;
symbol t_NRM9 (n m : ℕ) (P : Tuple n → Prop) (Q : Tuple n → Tuple m → Prop) (S : Prop)
  (h : π ((`♢ v : Tuple (n ++ m), P (take [n] [m] v) ⇒ Q (take [n] [m] v) (drop [n] [m] v)) ⇒ S))
  : π ((`♢ x : Tuple n, P x ⇒ (`!! y : Tuple m, Q x y)) ⇒ S) ≔ NRM9 h;

// ---- NRM10-15: implication / negation under ♢ and ♡ ----
symbol t_NRM10 (n : ℕ) (Ps : Tuple n → 𝕃* o) (Q : Tuple n → Prop) (R : Prop)
  (h : π ((`♡ v, ¬ ⋀ (Ps v ∷ Q v)) ⇒ R)) : π ((`♢ v, ⋀ (Ps v ∷ Q v) ⇒ ⊥) ⇒ R) ≔ NRM10 h;
symbol t_NRM11 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (h : π ((`♡ v, ¬ (⋀_snoc ⊤ (P v))) ⇒ R)) : π ((`♢ v, P v ⇒ ⊥) ⇒ R) ≔ NRM11 h;
symbol t_NRM12 (n : ℕ) (P Q : Tuple n → Prop) (R : Prop)
  (h : π ((`♡ v, ¬ ⋀_snoc (P v) (Q v)) ⇒ R)) : π ((`♢ v, P v ⇒ ¬ (Q v)) ⇒ R) ≔ NRM12 h;
symbol t_NRM13 (n : ℕ) (P Q : Tuple n → Prop) (R : Prop)
  (h : π ((`♡ v, ¬ ⋀_snoc (P v) (¬ (Q v))) ⇒ R)) : π ((`♢ v, P v ⇒ Q v) ⇒ R) ≔ NRM13 h;
symbol t_NRM14 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (h : π ((`♡ v, ¬ ⋀_snoc ⊤ (P v)) ⇒ R)) : π ((`♢ v, ¬ (P v)) ⇒ R) ≔ NRM14 h;
symbol t_NRM15 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (h : π ((`♡ v, ¬ ⋀_snoc ⊤ (¬ (P v))) ⇒ R)) : π ((`♢ v, P v) ⇒ R) ≔ NRM15 h;

// ---- NRM16-19: universal-instantiation patterns ----
symbol t_NRM16 (n : ℕ) (P : Tuple n → Prop) (Q : Prop)
  (h1 : π (`!! v, P v)) (h2 : π Q) : π ((`♡ v, P v) ⇒ Q) ≔ NRM16 h1 h2;
symbol t_NRM17 (n : ℕ) (P : Tuple n → Prop) (Q : Prop)
  (h1 : π (`!! v, P v)) (h2 : π Q) : π ((`♡ v, P v) ⇒ Q) ≔ NRM17 h1 h2;
symbol t_NRM18 (n : ℕ) (P : Tuple n → Prop) (R Q : Prop) (v : Tuple n)
  (h1 : π (`!! u, ¬ ⋀_snoc ⊤ (¬ P u))) (h2 : π (P v = R))
  : π ((`♡ _ : Tuple n, ¬ ⋀_snoc ⊤ R) ⇒ Q) ≔ NRM18 v h1 h2;
symbol t_NRM19 (n : ℕ) (Q : Prop) (R : Tuple n → Prop) (v : Tuple n)
  (h : π (R v)) : π ((`♡ u, ¬ ⋀_snoc ⊤ (R u)) ⇒ Q) ≔ NRM19 v h;

// ---- NRM20-23: substitution (binder pinned by an equality conjunct) ----
symbol t_NRM20 (n k : ℕ) (qs : Tuple (+1 n) → 𝕃* o) (Q : Prop) (E : Tuple n → τ ι)
  (h : π ((`♡ v' : Tuple n, ¬ ⋀ (qs (ins k (E v') v'))) ⇒ Q))
  : π ((`♡ v : Tuple (+1 n), ¬ ⋀ (qs v ∷ (prj k v = E (rm k v)))) ⇒ Q) ≔ NRM20 k E h;
symbol t_NRM21 (n k : ℕ) (qs : Tuple (+1 n) → 𝕃* o) (Q : Prop) (E : Tuple n → τ ι)
  (h : π ((`♡ v' : Tuple n, ¬ ⋀ (qs (ins k (E v') v'))) ⇒ Q))
  : π ((`♡ v : Tuple (+1 n), ¬ ⋀ (qs v ∷ (E (rm k v) = prj k v))) ⇒ Q) ≔ NRM21 k E h;
symbol t_NRM20H (n : ℕ) (ps : Tuple (+1 n) → 𝕃* o) (Q : Prop) (E : τ ι)
  (heq : Π v', π (popl (ps v') = (prj 0 v' = E)))
  (h : π ((`♡ v' : Tuple n, ¬ ⋀ dropl (ps (v' ⨾ E))) ⇒ Q))
  : π ((`♡ v : Tuple (+1 n), ¬ ⋀ (ps v)) ⇒ Q) ≔ NRM20H E heq h;
symbol t_NRM22 (Q : Prop) (ps : Tuple 1 → 𝕃* o) (E : τ ι)
  (h : π (¬ ⋀ (ps (unit ⨾ E)) ⇒ Q))
  : π ((`♡ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E))) ⇒ Q) ≔ NRM22 E h;
symbol t_NRM23 (Q : Prop) (E : τ ι) (h : π (¬ ⊤ ⇒ Q))
  : π ((`♡ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (E = prj 0 v))) ⇒ Q) ≔ NRM23 E h;
symbol t_NRM23G (Q : Prop) (ps : Tuple 1 → 𝕃* o) (E : τ ι)
  (h : π (¬ ⋀ (ps (unit ⨾ E)) ⇒ Q))
  : π ((`♡ v : Tuple 1, ¬ ⋀ (ps v ∷ (E = prj 0 v))) ⇒ Q) ≔ NRM23G E h;

// ---- NRM24-26: trivial structural rules ----
symbol t_NRM24 (n : ℕ) (P : Tuple n → Prop) (Q : Prop)
  (h : π ((`♡ v, ¬ ⋀ (∎ ∷ ⊤ ∷ P v)) ⇒ Q)) : π ((`♡ v, ¬ (P v)) ⇒ Q) ≔ NRM24 h;
symbol t_NRM25 (n : ℕ) (P Q : Prop) (h : π (P ⇒ Q)) : π ((`♡ _ : Tuple n, P) ⇒ Q) ≔ NRM25 h;
symbol t_NRM26 (n k : ℕ) (P : Tuple (+1 n) → Prop) (Q : Prop)
  (h : π ((`♡ v' : Tuple n, P (ins k (el ι) v')) ⇒ Q))
  : π ((`♡ v : Tuple (+1 n), P v) ⇒ Q) ≔ NRM26 k h;

// ---- NRM29: arithmetic solver dispatch (NRM27/28/30 fold onto this) ----
symbol t_NRM29 (n : ℕ) (ps : Tuple (+1 n) → 𝕃* o) (R : Prop) (b : Tuple n → τ ι)
  (h : π ((`♢ v' : Tuple n, ¬ ⋀ (ps (v' ⨾ b v'))) ⇒ R))
  : π ((`♡ v : Tuple (+1 n), ¬ ⋀ (ps v)) ⇒ R) ≔ NRM29 b h;

// ---- _1 (Result-form) variants ----
symbol t_NRM1_1 (n : ℕ) (P Q : Prop) (r : Res (P ⇒ Q))
  : Res ((`♢ _ : Tuple n, P) ⇒ Q) ≔ @NRM1_1 n P Q r;
symbol t_NRM2_1 (n : ℕ) (P : Prop) (Q : Tuple n → Prop) (S : Prop) (hp : π P)
  (r : Res ((`♢ v, Q v) ⇒ S)) : Res ((`♢ v, P ⇒ Q v) ⇒ S) ≔ NRM2_1 hp r;
symbol t_NRM3_1 (n : ℕ) (P : Tuple n → Prop) (Q S : Prop)
  (r : Res (⋀_snoc (Q ⇒ S) ((`!! v, ¬ (P v)) ⇒ S))) : Res ((`♢ v, P v ⇒ Q) ⇒ S) ≔ NRM3_1 r;
symbol t_NRM12_1 (n : ℕ) (P Q : Tuple n → Prop) (R : Prop)
  (r : Res ((`♡ v, ¬ ⋀_snoc (P v) (Q v)) ⇒ R)) : Res ((`♢ v, P v ⇒ ¬ (Q v)) ⇒ R) ≔ NRM12_1 r;
symbol t_NRM13_1 (n : ℕ) (P Q : Tuple n → Prop) (R : Prop)
  (r : Res ((`♡ v, ¬ ⋀_snoc (P v) (¬ Q v)) ⇒ R)) : Res ((`♢ v, P v ⇒ Q v) ⇒ R) ≔ NRM13_1 r;
symbol t_NRM14_1 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (r : Res ((`♡ v, ¬ ⋀_snoc ⊤ (P v)) ⇒ R)) : Res ((`♢ v, ¬ (P v)) ⇒ R) ≔ NRM14_1 r;
symbol t_NRM15_1 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (r : Res ((`♡ v, ¬ ⋀_snoc ⊤ (¬ (P v))) ⇒ R)) : Res ((`♢ v, P v) ⇒ R) ≔ NRM15_1 r;
symbol t_NRM22_1 (Q : Prop) (ps : Tuple 1 → 𝕃* o) (E : τ ι)
  (r : Res (¬ ⋀ (ps (unit ⨾ E)) ⇒ Q))
  : Res ((`♡ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E))) ⇒ Q) ≔ NRM22_1 r;
symbol t_NRM23_1 (Q : Prop) (E : τ ι) (r : Res (¬ ⊤ ⇒ Q))
  : Res ((`♡ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (E = prj 0 v))) ⇒ Q) ≔ @NRM23_1 Q E r;
