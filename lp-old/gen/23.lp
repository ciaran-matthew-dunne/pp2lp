require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|23.trace|} :
  Thm ((∀ ("a" ⨾ "b") (((¬ (∃ "x" (∃ "y" (papp "p" ("x" ↦ "y"))))) ∧ (∀ ("x$6" ⨾ "x$5") ((∃ "x$7" (("x$6" ↦ "x$5" ↦ "x$7") ∈ "p")) ⇒ (("x$6" ↦ "x$5" ↦ (eapp "p" ("x$6" ↦ "x$5"))) ∈ "p")))) ⇒ (¬ (papp "p" ("a" ↦ "b")))))) ≔
begin
  simplify;
  apply ALL8;
  apply AND3;
  apply XST1 ⊤ᵢ;
  apply XST5;
  apply ALL7
  { apply STOP_1 }
  { apply NRM14;
    apply ALL9;
    apply ALL7
    { apply XST7_1 ⊤ᵢ;
      apply ALL8_1;
      apply IMP4_1;
      apply STOP_1 }
    { apply NRM8 ⊤ᵢ;
      apply NRM13;
      apply ALL9;
      apply STOP;
      apply NOT1;
      apply AXM9 ("x" ⨾ "y") ("a" ↦ "b") ((papp "p" ("x" ↦ "y"))) ⊤ᵢ ⊤ᵢ } }
end;
