require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|27.trace|} :
  Thm ((∀ ("a" ⨾ "b") (((papp "p" ("a" ↦ "b")) ∧ (∀ ("x$6" ⨾ "x$5") ((∃ "x$7" (("x$6" ↦ "x$5" ↦ "x$7") ∈ "p")) ⇒ (("x$6" ↦ "x$5" ↦ (eapp "p" ("x$6" ↦ "x$5"))) ∈ "p")))) ⇒ (∃ "x" (∃ "y" (papp "p" ("x" ↦ "y"))))))) ≔
begin
  simplify;
  apply ALL8;
  apply AND3;
  apply IMP4;
  apply ALL7
  { apply XST7_1 ⊤ᵢ;
    apply ALL8_1;
    apply IMP4_1;
    apply STOP_1 }
  { apply NRM8 ⊤ᵢ;
    apply NRM13;
    apply ALL9;
    apply XST4 ⊤ᵢ;
    apply XST8
    { apply STOP_1 }
    { apply ALL7
      { apply STOP_1 }
      { apply NRM14;
        apply NRM19 ((papp "p" ("a" ↦ "b"))) ("a" ↦ "b") ⊤ᵢ ⊤ᵢ } } }
end;
