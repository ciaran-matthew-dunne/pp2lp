require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|26.trace|} :
  Thm ((∀ ("a" ⨾ "b") (("a" ≃ "b") ⇒ (∀ "x" (∀ "y" (("x" ≃ "y") ⇒ (("x" ≃ "a") ⇒ ("y" ≃ "b")))))))) ≔
begin
  simplify;
  apply ALL8;
  apply OPR1 ⊤ᵢ;
  apply ALL4 ⊤ᵢ;
  apply ALL8;
  apply OPR1 ⊤ᵢ;
  apply AXM7
end;
