require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|21.trace|} :
  Thm ((((∀ "x" (∀ "y" (papp "q" ("x" ↦ "y")))) ∧ (∀ ("x$6" ⨾ "x$5") ((∃ "x$7" (("x$6" ↦ "x$5" ↦ "x$7") ∈ "q")) ⇒ (("x$6" ↦ "x$5" ↦ (eapp "q" ("x$6" ↦ "x$5"))) ∈ "q")))) ⇒ ("p" ∨ (¬ "p")))) ≔
begin
  simplify;
  apply AND3;
  apply ALL3 ⊤ᵢ;
  apply ALL7
  { apply STOP_1 }
  { apply NRM15;
    apply ALL9;
    apply ALL7
    { apply XST7_1 ⊤ᵢ;
      apply ALL8_1;
      apply IMP4_1;
      apply STOP_1 }
    { apply NRM8 ⊤ᵢ;
      apply NRM13;
      apply ALL9;
      apply OR4;
      apply AXM7 } }
end;
