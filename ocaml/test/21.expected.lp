require open pp2lp.B pp2lp.Rules;

opaque symbol {|21|} (p : Prop) (q : τ ι) :
  π (⋀ (∎
     ∷ (`!! x_t : Tuple 2, (((prj 0 x_t) ↦ (prj 1 x_t)) ϵ q))
     ∷ (`!! {|x$6_t|} : Tuple 2,
          (`?? {|x$7_t|} : Tuple 1,
            ((prj 0 {|x$6_t|}) ↦ (prj 1 {|x$6_t|}) ↦ (prj 0 {|x$7_t|})) ϵ q)
          ⇒ ((prj 0 {|x$6_t|}) ↦ (prj 1 {|x$6_t|}) ↦ (eapp q ((prj 0 {|x$6_t|}) ↦ (prj 1 {|x$6_t|})))) ϵ q))
    ⇒ p ∨ ¬ p) ≔
begin
  assume p q;
  refine AND3 _;
  refine ALL7 (λ _x1, STOP_1) _;
  refine NRM15 _;
  refine ALL9 _;
  assume _h2;
  refine ALL7 (λ _x3, (XST7_1 (ALL8_1 (λ _x4, (IMP4_1 STOP_1))))) _;
  refine NRM8 _;
  refine NRM13 _;
  refine ALL9 _;
  assume _h5;
  refine OR4 _;
  refine AXM7
end;
