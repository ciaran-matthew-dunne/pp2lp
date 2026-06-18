require open pp2lp.Prelude;

opaque symbol {|18|} (p : Prop) :
  π ((`!! a_t : Tuple 1,
      let a ≔ (prj 0 a_t) in
      (`!! x_t : Tuple 1,
        let x ≔ (prj 0 x_t) in
        ¬ (⋀ (∎ ∷ ⊤ ∷ (x = x))))
      ⇒ a = a ⇒ p)) ≔
begin
  assume p;
  refine ALL8 _;
  assume _x1;
  refine ALL7 (λ _x2, (AND2_1 (VR3_1 (EVR2_1 STOP_1)))) _;
  refine NRM1 _;
  refine FX3
end;
