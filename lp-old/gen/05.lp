require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|05.trace|} :
  Thm (((¬ ("p" ∨ "q")) ⇒ (¬ "p"))) ≔
begin
  simplify;
  apply OR1;
  apply IMP4;
  apply AXM4 ⊤ᵢ
end;
