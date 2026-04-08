// Conjunction (§A.1)
require open
  pp2lp.B pp2lp.Eq
  pp2lp.Proof;

// Conjunction containment and removal.
sequential symbol contient : Prd → Prd → 𝔹;
notation contient infix 1;
rule contient ($P ∧ $Q) $R ↪ (contient $P $R) or (contient $Q $R)
with contient $P $Q ↪ prd_eq $P $Q;

sequential symbol retirer : Prd → Prd → Prd;
// ?retirer P Q R b: if P contains R (b=true), recurse left; else recurse right.
symbol ?retirer : Prd → Prd → Prd → 𝔹 → Prd;
// ??retirer L Q: rebuild conjunction, dropping TRUE (leaf removal marker).
sequential symbol ??retirer : Prd → Prd → Prd;
rule ??retirer TRUE $Q ↪ $Q
with ??retirer $P $Q ↪ $P ∧ $Q;
rule ?retirer $P $Q $R true ↪ ??retirer (retirer $R $P) $Q
with ?retirer $P $Q $R false ↪ $P ∧ (retirer $R $Q);
rule retirer $R ($P ∧ $Q) ↪ ?retirer $P $Q $R ($P contient $R)
with retirer _ _ ↪ TRUE;

// ---- Base rules ----

symbol AND1 [H P Q R]
  : ▷ (H ⟝ ¬ Q ⇒ R)
  → ▷ (H ⟝ ¬ P ⇒ R)
  → ▷ (H ⟝ ¬ (P ∧ Q) ⇒ R);

symbol AND2 [H P Q]
  : ▷ (H ⟝ P ⇒ ¬ Q)
  → ▷ (H ⟝ ¬ (P ∧ Q));

symbol AND3 [H P Q R]
  : ▷ (H ⟝ P ⇒ (Q ⇒ R))
  → ▷ (H ⟝ (P ∧ Q) ⇒ R);

symbol AND4 [H P Q]
  : ▷ (H ⟝ Q)
  → ▷ (H ⟝ P)
  → ▷ (H ⟝ P ∧ Q);
 //?/ ≔ begin simplify; print; end;

symbol AND5 [H C R] (A B : Prd)
  : ⁇ (C contient A)
  → ⁇ (C contient (A ⇒ B))
  → ▷ (H ⟝ ((retirer (A ⇒ B) C) ∧ B) ⇒ R)
  → ▷ (H ⟝ C ⇒ R);

// ---- Primed variants ----

symbol AND2_1 [H P Q]
  : Res (H ⟝ P ⇒ ¬ Q)
  → Res (H ⟝ ¬ (P ∧ Q));
rule obtain (AND2_1 $r) ↪ obtain $r;

symbol AND3_1 [H P Q R]
  : Res (H ⟝ P ⇒ (Q ⇒ R))
  → Res (H ⟝ (P ∧ Q) ⇒ R);
rule obtain (AND3_1 $r) ↪ obtain $r;

symbol AND5_1 [H C R] [A B : Prd]
  : ⁇ (C contient A)
  → ⁇ (C contient (A ⇒ B))
  → Res (H ⟝ ((retirer (A ⇒ B) C) ∧ B) ⇒ R)
  → Res (H ⟝ C ⇒ R);
rule obtain (AND5_1 _ _ $r) ↪ obtain $r;

symbol AND1_1 [H P Q R]
  : Res (H ⟝ ¬ Q ⇒ R)
  → Res (H ⟝ ¬ P ⇒ R)
  → Res (H ⟝ ¬ (P ∧ Q) ⇒ R);
rule obtain (AND1_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);

symbol AND4_1 [H P Q]
  : Res (H ⟝ Q)
  → Res (H ⟝ P)
  → Res (H ⟝ P ∧ Q);
rule obtain (AND4_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);
