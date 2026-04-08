require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|20.trace|} :
  Thm (((¬ (∀ "x" (∀ "y" ("x" ≃ "y")))) ⇒ ("p" ∨ (¬ "p")))) ≔
begin
  simplify;
  apply ALL1 ⊤ᵢ;
  apply ALL5 ⊤ᵢ;
  apply ALL8;
  apply IMP4;
  apply OR4;
  apply AXM7
end;
