require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|04.trace|} :
  Thm ((((("a" ∧ "p") ∧ ("p" ⇒ "q")) ∧ "c") ⇒ "q")) ≔
begin
  simplify;
  apply AND5 ("p") ("q") ⊤ᵢ ⊤ᵢ;
  apply AXM8 ⊤ᵢ
end;
