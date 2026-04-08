require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|06.trace|} :
  Thm ((¬ (("p" ∧ (¬ "p")) ∨ ("q" ∧ (¬ "q"))))) ≔
begin
  simplify;
  apply OR2
  { apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3 ⊤ᵢ }
  { apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3 ⊤ᵢ }
end;
