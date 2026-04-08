// Trace reconstructions using
// the PP inference rules.
require open
  pp2lp.rules.Conj pp2lp.rules.Disj
  pp2lp.rules.Impl pp2lp.rules.Equiv
  pp2lp.rules.Neg pp2lp.rules.Axm
  pp2lp.rules.All pp2lp.rules.Xst
  pp2lp.rules.TrueFalse
  pp2lp.rules.Nrm pp2lp.rules.Eq;
// shorthand: prove P from
// empty hypotheses.
symbol Thm (P : Prd) ≔ □ ⊩ P;

// Trace 01:
//   ¬(p ∧ q) ⇒ (¬p ∨ ¬q)
// [AND1]
//   {[IMP4] [OR4] [AXM4]}
//   {[IMP4] [OR4] [NOT1]
//    [AXM1]}
symbol {|01.trace|} :
  Thm (¬ ("p" ∧ "q") ⇒
    ((¬ "p") ∨ (¬ "q"))) ≔
begin
  simplify;
  apply AND1
  { apply IMP4;
    apply OR4;
    apply AXM4 ⊤ᵢ; }
  { apply IMP4;
    apply OR4;
    apply NOT1;
    apply AXM1 ⊤ᵢ }
end;
// Trace 02: ¬(p ∧ ¬p)
// [AND2] [IMP4] [NOT2] [AXM3]
symbol {|02.trace|} :
  Thm (¬ ("p" ∧ (¬ "p"))) ≔
begin
  simplify;
  apply AND2;
  apply IMP4;
  apply NOT2;
  apply AXM3 ⊤ᵢ
end;

// Trace 03:
//   (p ∧ q) ⇒ (q ∧ p)
// [AND3] [IMP4]
//   [AR10(q)] [IMP4] [AND4]
//   {[AXM3]} {[AXM3]}
symbol {|03.trace|} :
  Thm (("p" ∧ "q") ⇒
    ("q" ∧ "p")) ≔
begin
  simplify;
  apply AND3;
  apply IMP4;
  // AR10 is a no-op here
  // (solver confirms Q ≃ Q),
  // so just IMP4.
  apply IMP4;
  apply AND4
  { apply AXM3 ⊤ᵢ }
  { apply AXM3 ⊤ᵢ }
end;

// Trace 04:
//   (A ∧ P ∧ (P ⇒ Q) ∧ C)
//   ⇒ Q
// [AND5] [AXM8]
symbol {|04.trace|} :
  Thm (("a" ∧ "p"
    ∧ ("p" ⇒ "q") ∧ "c")
    ⇒ "q") ≔
begin
  simplify;
  apply AND5
    "p" "q" ⊤ᵢ ⊤ᵢ;
  apply AXM8 ⊤ᵢ
end;

// Trace 05:
//   ¬(p ∨ q) ⇒ ¬p
// [OR1] [IMP4] [AXM4]
symbol {|05.trace|} :
  Thm (¬ ("p" ∨ "q") ⇒
    ¬ "p") ≔
begin
  simplify;
  apply OR1;
  apply IMP4;
  apply AXM4 ⊤ᵢ
end;

// Trace 06:
//   ¬(p ∧ ¬p ∨ (q ∧ ¬q))
// [OR2]
//   {[AND2] [IMP4] [NOT2]
//    [AXM3]}
//   {[AND2] [IMP4] [NOT2]
//    [AXM3]}
symbol {|06.trace|} :
  Thm (¬ (("p" ∧ ¬ "p")
    ∨ ("q" ∧ ¬ "q"))) ≔
begin
  simplify;
  apply OR2
  { apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3 ⊤ᵢ }
  { apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3 ⊤ᵢ }
end;

// Trace 07:
//   (p ∨ q) ⇒ (q ∨ p)
// [OR3]
//   {[IMP4] [OR4] [AXM2]}
//   {[IMP4] [OR4] [AXM4]}
symbol {|07.trace|} :
  Thm (("p" ∨ "q") ⇒
    ("q" ∨ "p")) ≔
begin
  simplify;
  apply OR3
  { apply IMP4;
    apply OR4;
    apply AXM2 ⊤ᵢ }
  { apply IMP4;
    apply OR4;
    apply AXM4 ⊤ᵢ }
end;

// Trace 08:
//   ¬(p ⇒ q) ⇒ ¬q
// [IMP1] [IMP4] [AXM7]
symbol {|08.trace|} :
  Thm (¬ ("p" ⇒ "q") ⇒
    ¬ "q") ≔
begin
  simplify;
  apply IMP1;
  apply IMP4;
  apply AXM7
end;

// Trace 09:
//   ¬((p ∨ ¬p) ⇒ (p ∧ ¬p))
// [IMP2]
//   {[AND2] [IMP4] [NOT2]
//    [AXM3]}
//   {[OR4] [AXM7]}
symbol {|09.trace|} :
  Thm (¬ (("p" ∨ ¬ "p") ⇒
    ("p" ∧ ¬ "p"))) ≔
begin
  simplify;
  apply IMP2
  { apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3 ⊤ᵢ }
  { apply OR4;
    apply AXM7 }
end;

// Trace 10:
//   p ⇒ ¬p ⇒ ¬p
// [IMP3] {[AXM7]} {[AXM7]}
symbol {|10.trace|} :
  Thm ("p" ⇒
    (¬ "p") ⇒ (¬ "p")) ≔
begin
  simplify;
  apply IMP3
  { apply AXM7 }
  { apply AXM7 }
end;

// Trace 11:
//   p ⇒ (p ⇒ p ∧ p)
// [IMP4] [IMP5(1)] [AND4]
//   {[AXM3]} {[AXM3]}
symbol {|11.trace|} :
  Thm ("p" ⇒
    ("p" ⇒ ("p" ∧ "p"))) ≔
begin
  simplify;
  apply IMP4;
  apply IMP5 ⊤ᵢ;
  apply AND4
  { apply AXM3 ⊤ᵢ }
  { apply AXM3 ⊤ᵢ }
end;

// Trace 12:
//   ¬(p ⇔ p) ⇒ q
// [EQV1]
//   {[IMP4] [AXM2]}
//   {[IMP4] [AXM1]}
symbol {|12.trace|} :
  Thm (¬ ("p" ⇔ "p") ⇒
    "q") ≔
begin
  simplify;
  apply EQV1
  { apply IMP4;
    apply AXM2 ⊤ᵢ }
  { apply IMP4;
    apply AXM1 ⊤ᵢ }
end;

// Trace 13: ¬(p ⇔ ¬p)
// [EQV2]
//   {[IMP4] [NOT2] [AXM3]}
//   {[NOT1] [AXM7]}
symbol {|13.trace|} :
  Thm (¬ ("p" ⇔ ¬ "p")) ≔
begin
  simplify;
  apply EQV2
  { apply IMP4;
    apply NOT2;
    apply AXM3 ⊤ᵢ }
  { apply NOT1;
    apply AXM7 }
end;


// Trace 14:
//   (p ⇔ ¬p) ⇒ q
// [EQV3]
//   {[IMP4] [AXM2]}
//   {[IMP4] [NOT1] [AXM1]}
symbol {|14.trace|} :
  Thm (("p" ⇔ ¬ "p") ⇒
    "q") ≔
begin
  simplify;
  apply EQV3
  { apply IMP4;
    apply AXM2 ⊤ᵢ }
  { apply IMP4;
    apply NOT1;
    apply AXM1 ⊤ᵢ }
end;

// Trace 15: p ⇔ p
// [EQV4] {[AXM7]} {[AXM7]}
symbol {|15.trace|} :
  Thm ("p" ⇔ "p") ≔
begin
  simplify;
  apply EQV4
  { apply AXM7 }
  { apply AXM7 }
end;

// Trace 16:
//   ¬q ⇒ (p ⇒ (q ⇒ r))
// [IMP4] [AXM5]
symbol {|16.trace|} :
  Thm (¬ "q" ⇒
    ("p" ⇒
      ("q" ⇒ "r"))) ≔
begin
  simplify;
  apply IMP4;
  apply AXM5 ⊤ᵢ
end;

// Trace 17:
//   q ⇒ (p ⇒ (¬q ⇒ r))
// [IMP4] [AXM6]
symbol {|17.trace|} :
  Thm ("q" ⇒
    ("p" ⇒
      (¬ "q" ⇒ "r"))) ≔
begin
  simplify;
  apply IMP4;
  apply AXM6 ⊤ᵢ
end;

// Traces 18-27:
//   quantifier/set traces

// Trace 18:
//   ∀a.(∀x.¬(TRUE ∧ x ≃ x))
//   ⇒ (a ≃ a ⇒ p)
// [ALL8(1)] [ALL7(1)]
//   [FIN(FALSE)] [NRM1] [FX3]
symbol {|18.trace|} :
  Thm (∀ "a"
    ((∀ "x"
      (¬ (TRUE ∧
        ("x" ≃ "x"))))
    ⇒ ("a" ≃ "a" ⇒
      "p"))) ≔
begin
  simplify;
  apply ALL8;
  apply ALL7
  { apply AND2_1;
    apply VR3_1;
    apply EVR2_1;
    apply STOP_1 }
  { apply NRM1 ⊤ᵢ;
    apply FX3 }
end;

// Trace 19:
//   ∀a.(∀x.¬(TRUE ∧ p(x))
//   ∧ ∀(x$4).(∃(x$5).
//     (x$4,x$5: p)
//     ⇒ x$4,p(x$4): p)
//   ⇒ (p(a) ⇒ q))
symbol {|19.trace|} :
  Thm (∀ "a"
    ((∀ "x"
      (¬ (TRUE ∧
        papp "p" "x"))
    ∧ ∀ "x$4"
      (∃ "x$5"
        (("x$4" ↦ "x$5")
          ∈ "p")
      ⇒ ("x$4" ↦
        eapp "p" "x$4")
          ∈ "p"))
    ⇒ (papp "p" "a" ⇒
      "q"))) ≔
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
      apply AXM9
        "x" "a"
        (papp "p" "x")
        ⊤ᵢ ⊤ᵢ } }
end;

// Trace 20:
//   ¬(∀x.∀y.(x ≃ y))
//   ⇒ P ∨ ¬P
// [ALL1] [ALL5(2)]
//   [ALL8(1)] [IMP4]
//   [OR4] [AXM7]
symbol {|20.trace|} :
  Thm (¬ (∀ "x"
    (∀ "y"
      ("x" ≃ "y")))
    ⇒ "p" ∨ ¬ "p") ≔
begin
  simplify;
  apply ALL1 ⊤ᵢ;
  apply ALL5 ⊤ᵢ;
  apply ALL8;
  apply IMP4;
  apply OR4;
  apply AXM7
end;

// Trace 21:
//   ∀x.∀y.q(x,y) ∧ set_hyp
//   ⇒ p ∨ ¬p
symbol {|21.trace|} :
  Thm ((∀ "x"
    (∀ "y"
      (papp "q"
        ("x" ↦ "y")))
    ∧ ∀ ("x$6" ⨾ "x$5")
      (∃ "x$7"
        (("x$6" ↦ "x$5"
          ↦ "x$7") ∈ "q")
      ⇒ ("x$6" ↦ "x$5" ↦
        eapp "q"
          ("x$6" ↦ "x$5"))
        ∈ "q"))
    ⇒ "p" ∨ ¬ "p") ≔
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

// Trace 22:
//   ¬(∀x.∀y.¬(x ≃ x))
// [ALL2] [ALL6] [ALL7(1)]
//   [FIN(FAUX)] [NRM1]
//   [AXM7]
symbol {|22.trace|} :
  Thm (¬ (∀ "x"
    (∀ "y"
      (¬ ("x" ≃ "x"))))) ≔
begin
  simplify;
  apply ALL2 ⊤ᵢ;
  apply ALL6;
  apply ALL7
  { apply EVR2_1;
    apply STOP_1 }
  { apply NRM1 ⊤ᵢ;
    apply AXM7 }
end;

// Trace 23:
//   ∀(a,b).(¬(∃x.∃y.p(x,y))
//   ∧ set_hyp
//   ⇒ ¬p(a,b))
symbol {|23.trace|} :
  Thm (∀ ("a" ⨾ "b")
    ((¬ (∃ "x"
      (∃ "y"
        (papp "p"
          ("x" ↦ "y"))))
    ∧ ∀ ("x$6" ⨾ "x$5")
      (∃ "x$7"
        (("x$6" ↦ "x$5"
          ↦ "x$7") ∈ "p")
      ⇒ ("x$6" ↦ "x$5" ↦
        eapp "p"
          ("x$6" ↦ "x$5"))
        ∈ "p"))
    ⇒ ¬ (papp "p"
      ("a" ↦ "b")))) ≔
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
      apply AXM9
        ("x" ⨾ "y")
        ("a" ↦ "b")
        (papp "p"
          ("x" ↦ "y"))
        ⊤ᵢ ⊤ᵢ } }
end;

// Trace 24:
//   ∃x.∃y.p(x,y) ∧ set_hyp
//   ⇒ q ∨ ¬q
symbol {|24.trace|} :
  Thm ((∃ "x"
    (∃ "y"
      (papp "p"
        ("x" ↦ "y")))
    ∧ ∀ ("x$6" ⨾ "x$5")
      (∃ "x$7"
        (("x$6" ↦ "x$5"
          ↦ "x$7") ∈ "p")
      ⇒ ("x$6" ↦ "x$5" ↦
        eapp "p"
          ("x$6" ↦ "x$5"))
        ∈ "p"))
    ⇒ "q" ∨ ¬ "q") ≔
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

// Trace 25:
//   ∀(x$6,x$5).
//   (∃(x$7).
//     (x$6,x$5,x$7: p)
//     ⇒ x$6,x$5,
//       p(x$6,x$5): p)
//   ⇒ ¬(∃x.∃y.
//     (p(x,y) ∧ ¬p(x,y)))
symbol {|25.trace|} :
  Thm (∀ ("x$6" ⨾ "x$5")
    (∃ "x$7"
      (("x$6" ↦ "x$5"
        ↦ "x$7") ∈ "p")
    ⇒ ("x$6" ↦ "x$5" ↦
      eapp "p"
        ("x$6" ↦ "x$5"))
      ∈ "p")
    ⇒ ¬ (∃ "x"
      (∃ "y"
        (papp "p"
          ("x" ↦ "y")
        ∧ ¬ (papp "p"
          ("x" ↦
            "y")))))) ≔
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

// Trace 26:
//   ∀(a,b).(a ≃ b ⇒
//   ∀x.∀y.(x ≃ y ⇒
//     (x ≃ a ⇒ y ≃ b)))
// [ALL8(1)] [OPR1(1)]
//   [ALL4] [ALL8(1)]
//   [OPR1(1)] [AXM7]
symbol {|26.trace|} :
  Thm (∀ ("a" ⨾ "b")
    ("a" ≃ "b" ⇒
      ∀ "x" (∀ "y"
        ("x" ≃ "y" ⇒
          ("x" ≃ "a" ⇒
            "y" ≃
              "b"))))) ≔
begin
  simplify;
  apply ALL8;
  apply OPR1 ⊤ᵢ;
  apply ALL4 ⊤ᵢ;
  apply ALL8;
  apply OPR1 ⊤ᵢ;
  apply AXM7
end;

// Trace 27:
//   ∀(a,b).(p(a,b)
//   ∧ set_hyp
//   ⇒ ∃x.∃y.p(x,y))
symbol {|27.trace|} :
  Thm (∀ ("a" ⨾ "b")
    ((papp "p"
      ("a" ↦ "b")
    ∧ ∀ ("x$6" ⨾ "x$5")
      (∃ "x$7"
        (("x$6" ↦ "x$5"
          ↦ "x$7") ∈ "p")
      ⇒ ("x$6" ↦ "x$5" ↦
        eapp "p"
          ("x$6" ↦ "x$5"))
        ∈ "p"))
    ⇒ ∃ "x"
      (∃ "y"
        (papp "p"
          ("x" ↦
            "y"))))) ≔
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
        apply NRM19
          (papp "p"
            ("a" ↦ "b"))
          ("a" ↦ "b")
          ⊤ᵢ ⊤ᵢ } } }
end;

// TRUE/FALSE traces
// (28-30)

// Trace 28: ¬TRUE ⇒ p
// [VR1]
symbol {|28.trace|} :
  Thm (¬ TRUE ⇒ "p") ≔
begin
  simplify;
  apply VR1
end;

// Trace 29:
//   ¬FALSE ⇒ TRUE
// [FX1] [VR4]
symbol {|29.trace|} :
  Thm (¬ FALSE ⇒ TRUE) ≔
begin
  simplify;
  apply FX1;
  apply VR4
end;

// Trace 30: ¬FALSE
// [FX2]
symbol {|30.trace|} :
  Thm (¬ FALSE) ≔
begin
  simplify;
  apply FX2
end;
