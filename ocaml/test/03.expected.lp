require open pp2lp.B pp2lp.Rules;

opaque symbol {|03|} (p q : Prop) :
  π (⋀ (∎ ∷ p ∷ q) ⇒ ⋀ (∎ ∷ q ∷ p)) ≔
begin
  assume p q;
  refine AND3 _;
  refine IMP4 _;
  assume _h1;
  refine @AR10 _ (q) _ (eq_refl (q)) _;
  refine IMP4 _;
  assume _h2;
  refine AND4 _ _
  { refine AXM3 _h1 }
  { refine AXM3 _h2 }
end;
