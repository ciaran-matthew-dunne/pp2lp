require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|19.trace|} :
  Thm ((∀ "a" (((∀ "x" (¬ (TRUE ∧ (papp "p" "x")))) ∧ (∀ "x$4" ((∃ "x$5" (("x$4" ↦ "x$5") ∈ "p")) ⇒ (("x$4" ↦ (eapp "p" "x$4")) ∈ "p")))) ⇒ ((papp "p" "a") ⇒ "q")))) ≔
begin
  simplify;
  apply ALL8;
  apply AND3;
  apply ALL7
  { apply AND2_1;
    apply VR3_1;
    apply STOP_1 }
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
      apply AXM9 "x" "a" ((papp "p" "x")) ⊤ᵢ ⊤ᵢ } }
end;
