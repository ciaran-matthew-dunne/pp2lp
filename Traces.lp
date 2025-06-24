require open
  Logic.U.Set Logic.U.Prop Logic.U.Arrow;

require open
  pp2lp.Prelude pp2lp.Syntax;

require open
  pp2lp.rules.AXM pp2lp.rules.AND pp2lp.rules.OR
  pp2lp.rules.IMP pp2lp.rules.EQV pp2lp.rules.NOT;

symbol {|05.trace|} [p q] :
  ✓ (not (p or q) => not p) ≔
begin
  simplify;
  assume p q;
  simplify;
  apply OR1;
  apply IMP4;
  apply AXM4;
  simplify elem;
  refine TOP;
end;


symbol {|06.trace|} [p q] :
  ✓ (not (p and (not p) or (q and not q))) ≔
begin
  assume p q;
  simplify;
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


symbol {|07.trace|} [p q] :
  ✓ ((p or q) => (q or p)) ≔
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

symbol {|08.trace|} [p q] :
  ✓ (not (p => q) => not q) ≔
begin
  assume p q;
  simplify;
  apply IMP1;
  apply IMP4;
  apply AXM7;
end;


symbol {|09.trace|} [p] :
  ✓ (not ((p or not p) => (p and not p))) ≔
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
  ✓ (p => not p => not p) ≔
begin
  assume p;
  simplify;
  apply IMP3
  {
    apply AXM7;
  }{
    apply AXM7;
  };
end;
