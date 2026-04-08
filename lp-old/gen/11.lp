require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|11.trace|} :
  Thm (("p" ⇒ ("p" ⇒ ("p" ∧ "p")))) ≔
begin
  simplify;
  apply IMP4;
  apply IMP5 ⊤ᵢ;
  apply AND4
  { apply AXM3 ⊤ᵢ }
  { apply AXM3 ⊤ᵢ }
end;
