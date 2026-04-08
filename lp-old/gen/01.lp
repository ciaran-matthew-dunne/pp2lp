require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|01.trace|} :
  Thm (((¬ ("p" ∧ "q")) ⇒ ((¬ "p") ∨ (¬ "q")))) ≔
begin
  simplify;
  apply AND1
  { apply IMP4;
    apply OR4;
    apply AXM4 ⊤ᵢ }
  { apply IMP4;
    apply OR4;
    apply NOT1;
    apply AXM1 ⊤ᵢ }
end;
