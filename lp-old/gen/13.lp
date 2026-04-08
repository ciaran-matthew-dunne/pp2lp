require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|13.trace|} :
  Thm ((¬ ("p" ⇔ (¬ "p")))) ≔
begin
  simplify;
  apply EQV2
  { apply IMP4;
    apply NOT2;
    apply AXM3 ⊤ᵢ }
  { apply NOT1;
    apply AXM7 }
end;
