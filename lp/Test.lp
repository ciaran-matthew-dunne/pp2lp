// Test.lp — Hand-translated PP traces as shallow encoding proofs
require open pp2lp.B
  pp2lp.rules.Conj pp2lp.rules.Disj
  pp2lp.rules.Impl pp2lp.rules.Equiv
  pp2lp.rules.Neg pp2lp.rules.Axm
  pp2lp.rules.TrueFalse;

// ---- Trace 01 ----
// [AND1] <not(p and q) => not(p) or not(q)>
//   [IMP4] [OR4] [AXM4]
//   [IMP4] [OR4] [NOT1] [AXM1]

opaque symbol trace01 (p q : Prop) :
  π (¬ (p ∧ q) ⇒ (¬ p ∨ ¬ q)) ≔
begin
  assume p q;
  refine AND1 _ _ {
    // ¬q ⇒ ¬p ∨ ¬q
    refine IMP4 _;
    assume hnq;
    refine OR4 _;
    // goal: ¬(¬p) ⇒ ¬q — AXM4 closes with hnq
    refine AXM4 hnq
  } {
    // ¬p ⇒ ¬p ∨ ¬q
    refine IMP4 _;
    assume hnp;
    refine OR4 _;
    // goal: ¬(¬p) ⇒ ¬q — NOT1 then AXM1
    refine NOT1 _;
    // goal: p ⇒ ¬q — AXM1 closes with hnp
    refine AXM1 hnp
  }
end;

// ---- Trace 02 ----
// [AND2] [IMP4] [NOT2] [AXM3]

opaque symbol trace02 (p : Prop) :
  π (¬ (p ∧ ¬ p)) ≔
begin
  assume p;
  refine AND2 _;
  refine IMP4 _;
  assume hp;
  refine NOT2 hp
end;

// ---- Trace 12 ----
// [EQV1]
//   [IMP4] [AXM2]
//   [IMP4] [AXM1]

opaque symbol trace12 (p q : Prop) :
  π (¬ (p ⇔ p) ⇒ q) ≔
begin
  assume p q;
  refine EQV1 _ _ {
    // p ⇒ (¬p ⇒ q)
    refine IMP4 _;
    assume hp;
    refine AXM2 hp
  } {
    // ¬p ⇒ (p ⇒ q)
    refine IMP4 _;
    assume hnp;
    refine AXM1 hnp
  }
end;

// ---- Trace 28 ----
// [VR1]

opaque symbol trace28 (p : Prop) :
  π (¬ ⊤ ⇒ p) ≔
begin
  assume p;
  refine VR1
end;

// ---- Trace 30 ----
// [FX2]

opaque symbol trace30 :
  π (¬ ⊥) ≔
begin
  refine FX2
end;
