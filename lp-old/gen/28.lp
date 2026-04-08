require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|28.trace|} :
  Thm (((¬ TRUE) ⇒ "p")) ≔
begin
  simplify;
  apply VR1
end;
