require open pp2lp.B pp2lp.Int pp2lp.Rules;

opaque symbol {|01|} (p q : Prop) :
  π (¬ (⋀ (∎ ∷ p ∷ q)) ⇒ ¬ p ∨ ¬ q) ≔
begin
  assume p q;
  refine AND1 _ _
  { refine IMP4 _;
    assume _h1;
    refine OR4 _;
    refine AXM4 _h1 }
  { refine IMP4 _;
    assume _h2;
    refine OR4 _;
    refine NOT1 _;
    refine AXM1 _h2 }
end;
