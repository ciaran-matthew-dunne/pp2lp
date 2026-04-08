require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|18.trace|} :
  Thm ((∀ "a" ((∀ "x" (¬ (TRUE ∧ ("x" ≃ "x")))) ⇒ (("a" ≃ "a") ⇒ "p")))) ≔
begin
  simplify;
  apply ALL8;
  apply ALL7
  { apply AND2_1;
    apply VR3_1;
    apply EVR2_1;
    apply STOP_1 }
  { apply NRM1 ⊤ᵢ;
    apply FX3 }
end;
