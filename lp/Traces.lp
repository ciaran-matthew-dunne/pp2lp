// Traces.lp — PP trace reconstructions (shallow encoding)
require open pp2lp.B
  pp2lp.rules.Conj pp2lp.rules.Disj
  pp2lp.rules.Impl pp2lp.rules.Equiv
  pp2lp.rules.Neg pp2lp.rules.Axm
  pp2lp.rules.TrueFalse
  pp2lp.rules.All pp2lp.rules.Xst
  pp2lp.rules.Nrm pp2lp.rules.Eq
  pp2lp.rules.Arith pp2lp.rules.Rw;

// ---- Trace 01: ¬(p ∧ q) ⇒ (¬p ∨ ¬q) ----
opaque symbol {|01|} (p q : Prop) :
  π (¬ (p ∧ q) ⇒ (¬ p ∨ ¬ q)) ≔
begin
  assume p q;
  refine AND1 _ _
  { refine IMP4 _; assume hnq; refine OR4 _; refine AXM4 hnq }
  { refine IMP4 _; assume hnp; refine OR4 _; refine NOT1 _; refine AXM1 hnp }
end;

// ---- Trace 02: ¬(p ∧ ¬p) ----
opaque symbol {|02|} (p : Prop) :
  π (¬ (p ∧ ¬ p)) ≔
begin
  assume p;
  refine AND2 _; refine IMP4 _; assume hp; refine NOT2 hp
end;

// ---- Trace 03: (p ∧ q) ⇒ (q ∧ p) ----
// AR10(q) is a solver no-op; just IMP4.
opaque symbol {|03|} (p q : Prop) :
  π ((p ∧ q) ⇒ (q ∧ p)) ≔
begin
  assume p q;
  refine AND3 _; refine IMP4 _; assume hq;
  refine IMP4 _; assume hp;
  refine AND4 _ _ { refine AXM3 hq } { refine AXM3 hp }
end;

// ---- Trace 04: (a ∧ p ∧ (p ⇒ q) ∧ c) ⇒ q ----
// TODO: requires list-based AND5/AXM8 infrastructure.

// ---- Trace 05: ¬(p ∨ q) ⇒ ¬p ----
opaque symbol {|05|} (p q : Prop) :
  π (¬ (p ∨ q) ⇒ ¬ p) ≔
begin
  assume p q;
  refine OR1 _; refine IMP4 _; assume hnq; refine AXM4 hnq
end;

// ---- Trace 06: ¬(p ∧ ¬p ∨ (q ∧ ¬q)) ----
opaque symbol {|06|} (p q : Prop) :
  π (¬ ((p ∧ ¬ p) ∨ (q ∧ ¬ q))) ≔
begin
  assume p q;
  refine OR2 _ _
  { refine AND2 _; refine IMP4 _; assume hq; refine NOT2 hq }
  { refine AND2 _; refine IMP4 _; assume hp; refine NOT2 hp }
end;

// ---- Trace 07: (p ∨ q) ⇒ (q ∨ p) ----
opaque symbol {|07|} (p q : Prop) :
  π ((p ∨ q) ⇒ (q ∨ p)) ≔
begin
  assume p q;
  refine OR3 _ _
  { refine IMP4 _; assume hq; refine OR4 _; refine AXM2 hq }
  { refine IMP4 _; assume hp; refine OR4 _; refine AXM4 hp }
end;

// ---- Trace 08: ¬(p ⇒ q) ⇒ ¬q ----
opaque symbol {|08|} (p q : Prop) :
  π (¬ (p ⇒ q) ⇒ ¬ q) ≔
begin
  assume p q;
  refine IMP1 _; refine IMP4 _; assume hp; refine AXM7
end;

// ---- Trace 09: ¬((p ∨ ¬p) ⇒ (p ∧ ¬p)) ----
opaque symbol {|09|} (p : Prop) :
  π (¬ ((p ∨ ¬ p) ⇒ (p ∧ ¬ p))) ≔
begin
  assume p;
  refine IMP2 _ _
  { refine AND2 _; refine IMP4 _; assume hp; refine NOT2 hp }
  { refine OR4 _; refine AXM7 }
end;

// ---- Trace 10: (p ⇒ ¬p) ⇒ ¬p ----
opaque symbol {|10|} (p : Prop) :
  π ((p ⇒ ¬ p) ⇒ ¬ p) ≔
begin
  assume p;
  refine IMP3 _ _ { refine AXM7 } { refine AXM7 }
end;

// ---- Trace 11: p ⇒ (p ⇒ p ∧ p) ----
opaque symbol {|11|} (p : Prop) :
  π (p ⇒ (p ⇒ (p ∧ p))) ≔
begin
  assume p;
  refine IMP4 _; assume hp;
  refine IMP5 _;
  refine AND4 _ _ { refine AXM3 hp } { refine AXM3 hp }
end;

// ---- Trace 12: ¬(p ⇔ p) ⇒ q ----
opaque symbol {|12|} (p q : Prop) :
  π (¬ (p ⇔ p) ⇒ q) ≔
begin
  assume p q;
  refine EQV1 _ _
  { refine IMP4 _; assume hp; refine AXM2 hp }
  { refine IMP4 _; assume hnp; refine AXM1 hnp }
end;

// ---- Trace 13: ¬(p ⇔ ¬p) ----
opaque symbol {|13|} (p : Prop) :
  π (¬ (p ⇔ ¬ p)) ≔
begin
  assume p;
  refine EQV2 _ _
  { refine IMP4 _; assume hp; refine NOT2 hp }
  { refine NOT1 _; refine AXM7 }
end;

// ---- Trace 14: (p ⇔ ¬p) ⇒ q ----
opaque symbol {|14|} (p q : Prop) :
  π ((p ⇔ ¬ p) ⇒ q) ≔
begin
  assume p q;
  refine EQV3 _ _
  { refine IMP4 _; assume hp; refine AXM2 hp }
  { refine IMP4 _; assume hnp; refine NOT1 _; refine AXM1 hnp }
end;

// ---- Trace 15: p ⇔ p ----
opaque symbol {|15|} (p : Prop) :
  π (p ⇔ p) ≔
begin
  assume p;
  refine EQV4 _ _ { refine AXM7 } { refine AXM7 }
end;

// ---- Trace 16: ¬q ⇒ (p ⇒ (q ⇒ r)) ----
opaque symbol {|16|} (p q r : Prop) :
  π (¬ q ⇒ (p ⇒ (q ⇒ r))) ≔
begin
  assume p q r;
  refine IMP4 _; assume hnq; refine AXM5 hnq
end;

// ---- Trace 17: q ⇒ (p ⇒ (¬q ⇒ r)) ----
opaque symbol {|17|} (p q r : Prop) :
  π (q ⇒ (p ⇒ (¬ q ⇒ r))) ≔
begin
  assume p q r;
  refine IMP4 _; assume hq; refine AXM6 hq
end;

// ---- Trace 18: ∀a.(∀x.¬(⊤ ∧ x=x)) ⇒ (a=a ⇒ p) ----
// ALL7 with R(x) = ⊥ (result of normalising ¬(⊤∧x=x)).
opaque symbol {|18|} (p : Prop) :
  π (`∀ a : τ ι, (`∀ x : τ ι, ¬ (⊤ ∧ (x = x)))
    ⇒ ((a = a) ⇒ p)) ≔
begin
  assume p a;
  refine ALL7 (λ _, ⊥) _ _
  { assume x;
    refine AND2_1 (VR3_1 (EVR2_1 STOP_1)) }
  { refine NRM1 _; refine FX3 }
end;

// ---- Trace 20: ¬(∀x.∀y.(x = y)) ⇒ p ∨ ¬p ----
// ALL1 (identity), ALL5 (¬∀ elimination), IMP4, OR4, AXM7
opaque symbol {|20|} (p : Prop) :
  π (¬ (`∀ x : τ ι, `∀ y : τ ι, x = y) ⇒ (p ∨ ¬ p)) ≔
begin
  assume p;
  // ALL1 is identity in HOAS (∀x.∀y = ∀x.∀y)
  // ALL5 with P(x) = ∀y.(x=y), R = p ∨ ¬p
  refine ALL5 _; assume x;
  // Goal: ¬(∀y.x=y) ⇒ (p ∨ ¬p)
  refine IMP4 _; assume h0;
  refine OR4 _; refine AXM7
end;

// ---- Trace 22: ¬(∀x.∀y.¬(x = x)) ----
// ALL2/ALL6 (identity), ALL7 with R=⊥, NRM1, AXM7
opaque symbol {|22|} :
  π (¬ (`∀ x : τ ι, `∀ y : τ ι, ¬ (x = x))) ≔
begin
  // Goal: (∀x.∀y.¬(x=x)) ⇒ ⊥
  // ALL7 with P(x) = ∀y.¬(x=x), R(x) = ⊥
  refine ALL7 (λ _, ⊥) _ _
  { assume x;
    // Goal: (∀y.¬(x=x)) = ⊥
    // ∀y.¬(x=x) = ¬(x=x) (∀_const) = ⊥ (EVR2_1)
    rewrite ∀_const; refine EVR2_1 STOP_1 }
  { // Goal: (♢x.⊥) ⇒ ⊥ = (∀x.⊥) ⇒ ⊥
    refine NRM1 _; refine AXM7 }
end;

// ---- Trace 26: ∀(a,b).(a=b ⇒ ∀x.∀y.(x=y ⇒ (x=a ⇒ y=b))) ----
// ALL8, OPR1, ALL4 (identity), ALL8, OPR1, AXM7
opaque symbol {|26|} :
  π (`∀ a : τ ι, `∀ b : τ ι,
    (a = b) ⇒ (`∀ x : τ ι, `∀ y : τ ι,
      (x = y) ⇒ ((x = a) ⇒ (y = b)))) ≔
begin
  refine ALL8 _;
  assume a b;
  refine OPR1 (λ z, `∀ x : τ ι, `∀ y : τ ι, (x = y) ⇒ ((x = z) ⇒ (y = b))) _;
  // ALL4 is identity in HOAS
  refine ALL8 _;
  assume x y;
  refine OPR1 (λ z, (z = b) ⇒ (y = b)) _;
  refine AXM7
end;

// ---- Trace 28: ¬⊤ ⇒ p ----
opaque symbol {|28|} (p : Prop) :
  π (¬ ⊤ ⇒ p) ≔
begin
  assume p; refine VR1
end;

// ---- Trace 29: ¬⊥ ⇒ ⊤ ----
opaque symbol {|29|} :
  π (¬ ⊥ ⇒ ⊤) ≔
begin
  refine FX1 _; refine VR4
end;

// ---- Trace 30: ¬⊥ ----
opaque symbol {|30|} :
  π (¬ ⊥) ≔
begin
  refine FX2
end;
