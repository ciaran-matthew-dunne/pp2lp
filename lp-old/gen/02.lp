require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|02.trace|} :
  Thm ((¬ ("p" ∧ (¬ "p")))) ≔
begin
  simplify;
  apply AND2;
  apply IMP4;
  apply NOT2;
  apply AXM3 ⊤ᵢ
end;
