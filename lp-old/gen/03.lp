require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|03.trace|} :
  Thm ((("p" ∧ "q") ⇒ ("q" ∧ "p"))) ≔
begin
  simplify;
  apply AND3;
  apply IMP4;
  apply IMP4;
  apply AND4
  { apply AXM3 ⊤ᵢ }
  { apply AXM3 ⊤ᵢ }
end;
