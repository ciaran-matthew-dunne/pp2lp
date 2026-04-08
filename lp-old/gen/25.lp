require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|25.trace|} :
  Thm (((∀ ("x$6" ⨾ "x$5") ((∃ "x$7" (("x$6" ↦ "x$5" ↦ "x$7") ∈ "p")) ⇒ (("x$6" ↦ "x$5" ↦ (eapp "p" ("x$6" ↦ "x$5"))) ∈ "p"))) ⇒ (¬ (∃ "x" (∃ "y" ((papp "p" ("x" ↦ "y")) ∧ (¬ (papp "p" ("x" ↦ "y"))))))))) ≔
begin
  simplify;
  apply ALL7
  { apply XST7_1 ⊤ᵢ;
    apply ALL8_1;
    apply IMP4_1;
    apply STOP_1 }
  { apply NRM8 ⊤ᵢ;
    apply NRM13;
    apply ALL9;
    apply XST2 ⊤ᵢ;
    apply XST6;
    apply ALL8;
    apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3 ⊤ᵢ }
end;
