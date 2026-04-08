require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|22.trace|} :
  Thm ((¬ (∀ "x" (∀ "y" (¬ ("x" ≃ "x")))))) ≔
begin
  simplify;
  apply ALL2 ⊤ᵢ;
  apply ALL6;
  apply ALL7
  { apply EVR2_1;
    apply STOP_1 }
  { apply NRM1 ⊤ᵢ;
    apply AXM7 }
end;
