require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|29.trace|} :
  Thm (((¬ FALSE) ⇒ TRUE)) ≔
begin
  simplify;
  apply FX1;
  apply VR4
end;
