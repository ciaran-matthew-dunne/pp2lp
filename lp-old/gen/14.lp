require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|14.trace|} :
  Thm ((("p" ⇔ (¬ "p")) ⇒ "q")) ≔
begin
  simplify;
  apply EQV3
  { apply IMP4;
    apply AXM2 ⊤ᵢ }
  { apply IMP4;
    apply NOT1;
    apply AXM1 ⊤ᵢ }
end;
