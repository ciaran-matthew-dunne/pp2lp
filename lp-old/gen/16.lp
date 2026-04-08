require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|16.trace|} :
  Thm (((¬ "q") ⇒ ("p" ⇒ ("q" ⇒ "r")))) ≔
begin
  simplify;
  apply IMP4;
  apply AXM5 ⊤ᵢ
end;
