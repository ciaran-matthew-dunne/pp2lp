require open pp2lp.B pp2lp.Rules;

// Test 1: simple 2-element swap via rewrite
opaque symbol test_swap (P Q : Prop) : π ((P ∧ Q) = (Q ∧ P)) ≔
begin
  assume P Q;
  rewrite (∧_com P Q);
  reflexivity
end;

// Test 2: 3-element permutation needs ∧_com + propExt for reassociation
opaque symbol test_perm3 (A B C : Prop)
  : π (((A ∧ B) ∧ C) = ((C ∧ B) ∧ A)) ≔
begin
  assume A B C;
  rewrite (∧_com A B);
  rewrite (∧_com (B ∧ A) C);
  // C ∧ (B ∧ A) vs (C ∧ B) ∧ A — reassociate with propExt
  refine propExt _ _ _ _
  { assume h; refine ∧ᵢ (∧ᵢ (∧ₑ₁ h) (∧ₑ₁ (∧ₑ₂ h))) (∧ₑ₂ (∧ₑ₂ h)) }
  { assume h; refine ∧ᵢ (∧ₑ₁ (∧ₑ₁ h)) (∧ᵢ (∧ₑ₂ (∧ₑ₁ h)) (∧ₑ₂ h)) }
end;

// Test 3: ALL7 with explicit R, per-element via rewrites (fuzz_0008 case)
// Source body: (a ϵ U) ∧ ((x ϵ T) ∧ s)
// AND4 chain swaps to get: (s ∧ (x ϵ T)) ∧ (a ϵ U)
// Using rewrite ∧_com, Lambdapi handles association naturally.
opaque symbol test_all7_rw (s : Prop) (T U : τ ι) (x a : τ ι)
  (h0 : π (¬ (a ϵ U)))
  : π ((`♢ y : τ ι, (a ϵ U) ∧ ((x ϵ T) ∧ s)) ⇒ ⊥) ≔
begin
  assume s T U x a h0;
  refine ALL7 (λ _, (s ∧ (x ϵ T)) ∧ (a ϵ U)) _ _
  { assume y;
    rewrite (∧_com (a ϵ U) ((x ϵ T) ∧ s));
    rewrite (∧_com (x ϵ T) s);
    reflexivity }
  { refine NRM1 _;
    refine AND3 _;
    refine AXM5 h0 }
end;

// Test 4: same but R matches rewrite result (right-assoc)
// Instead of FIN-derived R, use what the rewrites actually produce.
opaque symbol test_all7_rw_ra (s : Prop) (T U : τ ι) (x a : τ ι)
  (h0 : π (¬ (a ϵ U)))
  : π ((`♢ y : τ ι, (a ϵ U) ∧ ((x ϵ T) ∧ s)) ⇒ ⊥) ≔
begin
  assume s T U x a h0;
  // R = (s ∧ x:T) ∧ a:U — what two ∧_com rewrites produce
  refine ALL7 (λ _, ((s ∧ (x ϵ T)) ∧ (a ϵ U))) _ _
  { assume y;
    rewrite (∧_com (a ϵ U) ((x ϵ T) ∧ s));
    rewrite (∧_com (x ϵ T) s);
    reflexivity }
  { refine NRM1 _;
    refine AND3 _;
    refine AXM5 h0 }
end;

// Test 5: What does rewrite actually produce? Use admit to inspect.
opaque symbol test_rw_inspect (s : Prop) (T U : τ ι) (x a : τ ι)
  : π (((a ϵ U) ∧ ((x ϵ T) ∧ s)) = ((a ϵ U) ∧ ((x ϵ T) ∧ s))) ≔
begin
  assume s T U x a;
  rewrite (∧_com (a ϵ U) ((x ϵ T) ∧ s));
  rewrite (∧_com (x ϵ T) s);
  // What's the goal now?
  admit
end;
