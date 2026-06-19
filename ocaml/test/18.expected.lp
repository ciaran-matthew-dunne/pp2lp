require open pp2lp.Prelude;

opaque symbol {|18|} (p : Prop) :
  π ((`!! a_t : Tuple 1,
      (`!! x_t : Tuple 1,
        ¬ (⋀ (∎ ∷ ⊤ ∷ ((x_t ⋕ 0) = (x_t ⋕ 0)))))
      ⇒ (a_t ⋕ 0) = (a_t ⋕ 0) ⇒ p)) ≔
begin
  assume p;
  refine ALL8 _;
  assume _x1;
  refine ALL7 (λ _x2, (AND2_1 (VR3_1 (EVR2_1 STOP_1)))) _;
  refine NRM1 _;
  refine FX3
end;
