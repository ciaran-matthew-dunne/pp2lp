require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|07.trace|} :
  Thm ((("p" ∨ "q") ⇒ ("q" ∨ "p"))) ≔
begin
  simplify;
  apply OR3
  { apply IMP4;
    apply OR4;
    apply AXM2 ⊤ᵢ }
  { apply IMP4;
    apply OR4;
    apply AXM4 ⊤ᵢ }
end;
