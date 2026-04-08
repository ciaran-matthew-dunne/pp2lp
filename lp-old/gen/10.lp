require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|10.trace|} :
  Thm ((("p" ⇒ (¬ "p")) ⇒ (¬ "p"))) ≔
begin
  simplify;
  apply IMP3
  { apply AXM7 }
  { apply AXM7 }
end;
