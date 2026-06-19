require open pp2lp.Prelude;

opaque symbol {|21|} (p : Prop) (q : τ ι) :
  π (⋀ (∎
     ∷ (`!! x_t : Tuple 1,
          (`!! y_t : Tuple 1, (((x_t ⋕ 0) ↦ (y_t ⋕ 0)) ϵ q)))
     ∷ (`!! x6_t : Tuple 2,
          (`?? x7_t : Tuple 1,
            ((x6_t ⋕ 0) ↦ (x6_t ⋕ 1) ↦ (x7_t ⋕ 0)) ϵ q)
          ⇒ ((x6_t ⋕ 0) ↦ (x6_t ⋕ 1) ↦ (eapp q ((x6_t ⋕ 0) ↦ (x6_t ⋕ 1)))) ϵ q))
    ⇒ p ∨ ¬ p) ≔
begin
  assume p q;
  refine AND3 _;
  refine ALL3 _;
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
