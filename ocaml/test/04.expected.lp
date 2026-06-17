require open pp2lp.Prelude;

opaque symbol {|04|} (a c p q : Prop) :
  π (⋀ (∎ ∷ a ∷ p ∷ (p ⇒ q) ∷ c) ⇒ q) ≔
begin
  assume a c p q;
  refine AND5 (λ _h1, (⋀_intro (⋀_intro (⋀_intro (⋀_intro ⋀_nil_prf (⋀_init (⋀_init (⋀_init _h1)))) (⋀_last (⋀_init (⋀_init _h1)))) (⋀_last _h1)) ((⋀_last (⋀_init _h1)) (⋀_last (⋀_init (⋀_init _h1)))))) _;
  refine AXM8 (λ _h2, (⋀_last _h2))
end;
