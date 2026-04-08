require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|09.trace|} :
  Thm ((¬ (("p" ∨ (¬ "p")) ⇒ ("p" ∧ (¬ "p"))))) ≔
begin
  simplify;
  apply IMP2
  { apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3 ⊤ᵢ }
  { apply OR4;
    apply AXM7 }
end;
