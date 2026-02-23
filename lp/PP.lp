require Stdlib.Prop as P;
require open Stdlib.Classic;
require open pp2lp.B pp2lp.Eq;

// `Set`-level encodings for `Prd` and `Exp`.
symbol prd : Set; rule τ prd ↪ Prd;
symbol exp : Set; rule τ exp ↪ Exp;

inductive Hyp : TYPE ≔
  | ⦳ : Hyp
  | ∷ : Hyp → Prd → Hyp;

notation ∷ infix 1;

symbol dans : Prd → Hyp → 𝔹;
notation dans infix 1;

rule ($P dans ⦳)         ↪ false
with ($P dans ($H ∷ $Q)) ↪ prd_eq $P $Q or ($P dans $H);

symbol Sqnt : TYPE;
symbol ⟝ : Hyp → Prd → Sqnt; notation ⟝ infix 1;
symbol ▷ : Sqnt → TYPE;

// boolean guard: `⁇ b` is inhabited iff `b` computes to `true`.
symbol ⁇ (b : 𝔹) ≔ π (istrue b);

symbol ⊩ ≔ λ H P, ▷ (H ⟝ P);
notation ⊩ infix 1;

symbol contient : Prd → Prd → 𝔹;
notation contient infix 1;

// search for X in the leaves of a conjunction tree.
rule (($Qs ∧ $Q) contient $X) ↪ prd_eq $X $Q or ($Qs contient $X)
with (_ contient $X) ↪ false;

// remove the first occurrence of X in clause C (right-to-left search).
symbol retirer : Prd → Prd → Prd;
rule retirer $X ($Cs ∧ $Q)
  ↪ if (prd_eq $X $Q) [prd] $Cs
      (if (prd_eq $X $Cs) [prd] $Q ((retirer $X $Cs) ∧ $Q));

symbol prop : Prd → Prop;
rule prop (¬ $P)    ↪ (P.¬) (prop $P)
with prop ($P ∧ $Q) ↪ (P.∧) (prop $P) (prop $Q)
with prop ($P ∨ $Q) ↪ (P.∨) (prop $P) (prop $Q)
with prop ($P ⇒ $Q) ↪ (P.⇒) (prop $P) (prop $Q)
with prop ($P ⇔ $Q) ↪ (P.⇔) (prop $P) (prop $Q);

symbol props : Hyp → Prop;
rule props (⦳)       ↪ ⊤
with props ($H ∷ $P) ↪ (P.∧) (props $H) (prop $P);

rule ▷ ($H ⟝ $P) ↪ π (props $H) → π (prop $P);

// induction principle on hyp-lists
symbol Hyp_ind (M : Hyp → Prop)
  : π (M ⦳) → (Π H, π (M H) → Π Q, π (M (H ∷ Q))) → Π H, π (M H) ≔
begin
  assume M base step;
  induction
  { refine base }
  { assume H ih Q; refine step H ih Q }
end;


// ---- conjunction ----------------
opaque symbol AND1 [H P Q R]
  : (H ⊩ ¬ Q ⇒ R) → (H ⊩ ¬ P ⇒ R) → (H ⊩ ¬ (P ∧ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify;
  assume one two h npq;
  apply ∨ₑ (em (prop P))
  { assume hp; refine one h (λ hq, npq (∧ᵢ hp hq)) }
  { assume hnp; refine two h hnp }
end;

opaque symbol AND2 [H P Q]
  : (H ⊩ P ⇒ ¬ Q) → (H ⊩ ¬ (P ∧ Q)) ≔
begin
  assume H P Q; simplify;
  assume one h pq;
  refine one h (∧ₑ₁ pq) (∧ₑ₂ pq)
end;

opaque symbol AND3 [H P Q R]
  : (H ⊩ P ⇒ (Q ⇒ R)) → (H ⊩ (P ∧ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify;
  assume one h pq;
  refine one h (∧ₑ₁ pq) (∧ₑ₂ pq)
end;


opaque symbol AND4 [H P Q]
  : (H ⊩ Q) → (H ⊩ P) → (H ⊩ P ∧ Q) ≔
begin
  assume H P Q; simplify;
  assume one two h;
  refine ∧ᵢ (two h) (one h)
end;

// AND5 — propositional version.
opaque symbol AND5p [H P Q A B R]
  : (π (prop (P ∧ Q)) → π ((prop (retirer (A ⇒ B) (P ∧ Q))) P.∧ (prop (A ⇒ B))))
  → (π (prop (retirer (A ⇒ B) (P ∧ Q))) → π (prop A))
  → (H ⊩ retirer (A ⇒ B) (P ∧ Q) ∧ B ⇒ R)
  → (H ⊩ (P ∧ Q) ⇒ R) ≔
begin
  assume H P Q A B R split extract_a sub;
  simplify; assume h pq;
  have s : π ((prop (retirer (A ⇒ B) (P ∧ Q))) P.∧ (prop (A ⇒ B)))
    { refine split pq };
  set rem ≔ P.∧ₑ₁ s;
  set imp ≔ P.∧ₑ₂ s;
  have ha : π (prop A) { refine extract_a rem };
  have hb : π (prop B) { refine imp ha };
  refine sub h (P.∧ᵢ rem hb)
end;

// AND5 — computational wrapper.
symbol AND5 [H P Q A B R]
  : ⁇ ((P ∧ Q) contient (A ⇒ B))
  → ⁇ (retirer (A ⇒ B) (P ∧ Q) contient A)
  → (H ⊩ retirer (A ⇒ B) (P ∧ Q) ∧ B ⇒ R)
  → (H ⊩ (P ∧ Q) ⇒ R);

// ---- disjunction ----------------
opaque symbol OR1 [H P Q R]
  : (H ⊩ ¬ P ⇒ (¬ Q ⇒ R)) → (H ⊩ ¬ (P ∨ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify; assume one h npq;
  refine one h (λ hp, npq (∨ᵢ₁ hp)) (λ hq, npq (∨ᵢ₂ hq))
end;

opaque symbol OR2 [H P Q]
  : (H ⊩ ¬ Q) → (H ⊩ ¬ P) → (H ⊩ ¬ (P ∨ Q)) ≔
begin
  assume H P Q; simplify; assume one two h pq;
  apply ∨ₑ pq
  { assume hp; refine two h hp }
  { assume hq; refine one h hq }
end;

opaque symbol OR3 [H P Q R]
  : (H ⊩ Q ⇒ R) → (H ⊩ P ⇒ R) → (H ⊩ (P ∨ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify; assume one two h pq;
  apply ∨ₑ pq
  { assume hp; refine two h hp }
  { assume hq; refine one h hq }
end;

opaque symbol OR4 [H P Q]
  : (H ⊩ ¬ P ⇒ Q) → (H ⊩ P ∨ Q) ≔
begin
  assume H P Q; simplify; assume one h;
  apply ∨ₑ (em (prop P))
  { assume hp; refine ∨ᵢ₁ hp }
  { assume hnp; refine ∨ᵢ₂ (one h hnp) }
end;

// ---- implication ----------------
opaque symbol IMP1 [H P Q R]
  : (H ⊩ P ⇒ ((¬ Q) ⇒ R)) → (H ⊩ (¬ (P ⇒ Q)) ⇒ R) ≔
begin
  assume H P Q R; simplify; assume one h npq;
  apply ∨ₑ (em (prop Q))
  { assume hq; refine ⊥ₑ (npq (λ _, hq)) }
  { assume hnq;
    apply ∨ₑ (em (prop P))
    { assume hp; refine one h hp hnq }
    { assume hnp; refine ⊥ₑ (npq (λ hp, ⊥ₑ (hnp hp))) } }
end;

opaque symbol IMP2 [H P Q]
  : (H ⊩ ¬ Q) → (H ⊩ P) → (H ⊩ ¬ (P ⇒ Q)) ≔
begin
  assume H P Q; simplify; assume one two h p;
  refine (one h) (p (two h))
end;

opaque symbol IMP3 [H P Q R]
  : (H ⊩ Q ⇒ R) → (H ⊩ (¬ P) ⇒ R) → (H ⊩ (P ⇒ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify; assume one two h pq;
  apply ∨ₑ (em (prop P))
  { assume hp; refine one h (pq hp) }
  { assume hnp; refine two h hnp }
end;

opaque symbol IMP4 [H P Q]
  : ((H ∷ P) ⊩ Q) → (H ⊩ P ⇒ Q) ≔
begin
  assume H P Q; assume hp h p;
  refine hp (∧ᵢ h p)
end;

// IMP5 — propositional version.
opaque symbol IMP5p [H P Q]
  : (π (props H) → π (prop P)) → (H ⊩ Q) → (H ⊩ P ⇒ Q) ≔
begin
  assume H P Q lookup one; simplify; assume h p;
  refine one h
end;

// IMP5 — computational wrapper.
symbol IMP5 [H P Q]
  : ⁇ (P dans H) → (H ⊩ Q) → (H ⊩ P ⇒ Q);

// ---- equivalence ----------------
opaque symbol EQV1 [H P Q R]
  : (H ⊩ P ⇒ (¬ Q ⇒ R)) → (H ⊩ ¬ P ⇒ (Q ⇒ R))
  → (H ⊩ ¬ (P ⇔ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify;
  assume one two h npq;
  apply ∨ₑ (em (prop P))
  { assume hp;
    refine one h hp (λ hq, npq (∧ᵢ (λ _, hq) (λ _, hp))) }
  { assume hnp;
    apply ∨ₑ (em (prop Q))
    { assume hq; refine two h hnp hq }
    { assume hnq; refine one h (¬¬ₑ _ (λ np, npq (∧ᵢ (λ hp, ⊥ₑ (np hp)) (λ hq, ⊥ₑ (hnq hq))))) hnq } }
end;

opaque symbol EQV2 [H P Q]
  : (H ⊩ P ⇒ ¬ Q) → (H ⊩ ¬ Q ⇒ P) → (H ⊩ ¬ (P ⇔ Q)) ≔
begin
  assume H P Q; simplify; assume one two h pq;
  set pq1 ≔ ∧ₑ₁ pq; set pq2 ≔ ∧ₑ₂ pq;
  apply ∨ₑ (em (prop Q))
  { assume hq; refine one h (pq2 hq) hq }
  { assume hnq; refine one h (two h hnq) (pq1 (two h hnq)) }
end;

opaque symbol EQV3 [H P Q R]
  : (H ⊩ P ⇒ (Q ⇒ R)) → (H ⊩ ¬ P ⇒ (¬ Q ⇒ R))
  → (H ⊩ (P ⇔ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify; assume one two h pq;
  set pq1 ≔ ∧ₑ₁ pq; set pq2 ≔ ∧ₑ₂ pq;
  apply ∨ₑ (em (prop P))
  { assume hp; refine one h hp (pq1 hp) }
  { assume hnp; refine two h hnp (λ hq, ⊥ₑ (hnp (pq2 hq))) }
end;

opaque symbol EQV4 [H P Q]
  : (H ⊩ P ⇒ Q) → (H ⊩ Q ⇒ P) → (H ⊩ P ⇔ Q) ≔
begin
  assume H P Q; simplify; assume one two h;
  refine ∧ᵢ (one h) (two h)
end;

// ---- negation ----------------
opaque symbol NOT1 [H P R]
  : (H ⊩ P ⇒ R) → (H ⊩ ¬ ¬ P ⇒ R) ≔
begin
  assume H P R; simplify; assume one h nnp;
  refine one h (¬¬ₑ _ nnp)
end;

opaque symbol NOT2 [H P]
  : (H ⊩ P) → (H ⊩ ¬ ¬ P) ≔
begin
  assume H P; simplify; assume one h np;
  refine np (one h)
end;

// ---- 'axioms' --------
symbol AXM1 [H P Q] : ⁇ (¬ P dans H) → (H ⊩ P ⇒ Q);
symbol AXM2 [H P Q] : ⁇ (P dans H) → (H ⊩ ¬ P ⇒ Q);
symbol AXM3 [H P] : ⁇ (P dans H) → (H ⊩ P);
symbol AXM4 [H P R] : ⁇ (R dans H) → (H ⊩ P ⇒ R);
symbol AXM5 [H P Q R] : ⁇ (¬ Q dans H) → (H ⊩ P ⇒ (Q ⇒ R));
symbol AXM6 [H P Q R] : ⁇ (Q dans H) → (H ⊩ P ⇒ (¬ Q ⇒ R));
symbol AXM8 [H C R] : ⁇ (C contient R) → (H ⊩ C ⇒ R);
