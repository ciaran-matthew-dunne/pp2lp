require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|12.trace|} :
  Thm (((¬ ("p" ⇔ "p")) ⇒ "q")) ≔
begin
  simplify;
  apply EQV1
  { apply IMP4;
    apply AXM2 ⊤ᵢ }
  { apply IMP4;
    apply AXM1 ⊤ᵢ }
end;
