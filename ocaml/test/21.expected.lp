require open pp2lp.Prelude;

opaque symbol {|21|} (p : Prop) (q : τ ι) :
  π (⋀ (∎
     ∷ (`!! x_t : Tuple 2,
          let x ≔ (prj 0 x_t) in
          let y ≔ (prj 1 x_t) in
          (x ↦ y) ϵ q)
     ∷ (`!! x6_t : Tuple 2,
          let x6 ≔ (prj 0 x6_t) in
          let x5 ≔ (prj 1 x6_t) in
          (`?? x7_t : Tuple 1,
            let x7 ≔ (prj 0 x7_t) in
            (x6 ↦ x5 ↦ x7) ϵ q)
          ⇒ (x6 ↦ x5 ↦ (eapp q (x6 ↦ x5))) ϵ q))
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
