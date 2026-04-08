require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|24.trace|} :
  Thm ((((∃ "x" (∃ "y" (papp "p" ("x" ↦ "y")))) ∧ (∀ ("x$6" ⨾ "x$5") ((∃ "x$7" (("x$6" ↦ "x$5" ↦ "x$7") ∈ "p")) ⇒ (("x$6" ↦ "x$5" ↦ (eapp "p" ("x$6" ↦ "x$5"))) ∈ "p")))) ⇒ ("q" ∨ (¬ "q")))) ≔
begin
  simplify;
  apply AND3;
  apply XST3 ⊤ᵢ;
  apply XST7 ⊤ᵢ;
  apply ALL8;
  apply IMP4;
  apply ALL7
  { apply XST7_1 ⊤ᵢ;
    apply ALL8_1;
    apply IMP4_1;
    apply STOP_1 }
  { apply NRM8 ⊤ᵢ;
    apply NRM13;
    apply ALL9;
    apply OR4;
    apply AXM7 }
end;
