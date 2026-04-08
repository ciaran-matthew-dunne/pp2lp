require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|15.trace|} :
  Thm (("p" ⇔ "p")) ≔
begin
  simplify;
  apply EQV4
  { apply AXM7 }
  { apply AXM7 }
end;
