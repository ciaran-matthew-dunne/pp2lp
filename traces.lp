require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.pp;

symbol {|05.trace|} [p q] : thm (¬ (p ∨ q) ⇒ ¬ p)
  ≔
  begin
    assume p q; simplify;
    apply OR1;
    apply IMP4;
    apply AXM4;
    simplify elem;
    refine TOP;
  end;

symbol {|06.trace|} [p q] : thm (¬ (p ∧ (¬ p) ∨ (q ∧ ¬ q)))
  ≔
  begin
    assume p q; simplify;
    apply OR2
    {
      apply AND2;
      apply IMP4;
      apply NOT2;
      apply AXM3;
      simplify elem;
      refine TOP;
    }{
      apply AND2;
      apply IMP4;
      apply NOT2;
      apply AXM3;
      simplify elem;
      refine TOP;
    };
  end;


symbol {|07.trace|} [p q] : thm ((p ∨ q) ⇒ (q ∨ p))
  ≔
  begin
    assume p q;
    simplify;
    apply OR3
    {
      apply IMP4;
      apply OR4;
      apply AXM2;
      simplify elem;
      refine TOP;
    }{
      apply IMP4;
      apply OR4;
      apply AXM4;
      simplify elem;
      refine TOP;
    };
  end;

symbol {|08.trace|} [p q] : thm (¬ (p ⇒ q) ⇒ ¬ q)
  ≔
  begin
    assume p q;
    simplify;
    apply IMP1;
    apply IMP4;
    apply AXM7;
  end;


symbol {|09.trace|} [p] :
thm (¬ ((p ∨ ¬ p) ⇒ (p ∧ ¬ p)))
  ≔
  begin
    assume p;
    simplify;
    apply IMP2
    {
      apply AND2;
      apply IMP4;
      apply NOT2;
      apply AXM3;
      simplify elem;
      refine TOP;
    }{
      apply OR4;
      apply AXM7;
    };
  end;

  symbol {|10.trace|} [p] :
  thm (p ⇒ ¬ p ⇒ ¬ p)
    ≔
    begin
      assume p;
      simplify;
      apply IMP3
      {
        apply AXM7;
      } {
        apply AXM7;
      };
    end;
