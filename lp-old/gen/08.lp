require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|08.trace|} :
  Thm (((¬ ("p" ⇒ "q")) ⇒ (¬ "q"))) ≔
begin
  simplify;
  apply IMP1;
  apply IMP4;
  apply AXM7
end;
