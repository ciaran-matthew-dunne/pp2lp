require open pp2lp.B pp2lp.Quant;

type take;
type drop;

require open pp2lp.B pp2lp.Rules;

opaque symbol {|24|} (q : Prop) (p : τ ι) :
  π ((`?? x_t : Tuple 2, (((prj 0 x_t) ↦ (prj _1 x_t)) ϵ p))
    ∧ (`!! {|x$6_t|} : Tuple 2,
        (`?? {|x$7_t|} : Tuple 1,
          ((prj 0 {|x$6_t|}) ↦ (prj _1 {|x$6_t|}) ↦ (prj 0 {|x$7_t|})) ϵ p)
        ⇒ ((prj 0 {|x$6_t|}) ↦ (prj _1 {|x$6_t|}) ↦ (eapp p ((prj 0 {|x$6_t|}) ↦ (prj _1 {|x$6_t|})))) ϵ p)
    ⇒ q ∨ ¬ q) ≔
begin
  assume q p;
  // AND3
  refine AND3 _;
  // XST7
  refine XST7 _;
  // ALL8
  refine ALL8 _;
  assume x_t;
  // IMP4
  refine IMP4 _;
  assume h0;
  // ALL7
  refine ALL7 _ _
  { assume {|x$6_t|};
    // XST7_1
    refine XST7_1 _;
    // ALL8_1
    refine ALL8_1 _;
    assume {|x$7_t|};
    // IMP4_1
    refine IMP4_1 _;
    // STOP_1
    refine STOP_1 }
  {
    simplify; print;
    print;
    refine NRM8 _;
    // NRM13
    refine NRM13 _;
    // ALL9
    refine ALL9 _;
    assume h1;
    // OR4
    refine OR4 _;
    // AXM7
    refine AXM7 }
end;
