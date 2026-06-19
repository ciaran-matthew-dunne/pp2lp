require open pp2lp.Prelude;

opaque symbol {|04|} (a c p q : Prop) :
  π (⋀ (∎ ∷ a ∷ p ∷ (p ⇒ q) ∷ c) ⇒ q) ≔
begin
  assume a c p q;
  refine AND5 (λ _h1, (⋀_intro (conj_rm _ 1 _h1) ((conj_prj _ 1 _h1) (conj_prj _ 2 _h1)))) _;
  refine AXM8 (λ _h2, (conj_prj _ 0 _h2))
end;
