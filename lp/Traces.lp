require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax pp2lp.Rules;

coerce_rule coerce String (El exp) $x ↪ var $x;
assert ⊢ ("x") : El exp;

symbol {|01.trace|} [p q : El prd] :
  Thm (not (p and q) => ((not p) or (not q))) ≔
begin
  assume p q;
  apply AND1
  {
    apply IMP4;
    apply OR4;
    apply AXM4
  } {
    apply IMP4;
    apply OR4;
    apply NOT1;
    apply AXM1
  }
end;

symbol {|02.trace|} [p] :
  Thm (not (p and (not p))) ≔
begin
  assume p;
  apply AND2;
  apply IMP4;
  apply NOT2;
  apply AXM3
end;

symbol {|03.trace|} [p q] :
  Thm ((p and q) => (q and p)) ≔
begin
  assume p q;
  apply AND3;
  apply IMP4
  //apply AR10;
abort;

symbol {|04.trace|} [a c p q] :
  Thm (a and p and (p => q) and (c => q)) ≔
begin
  assume a c p q
abort;


symbol {|05.trace|} [p q] :
  Thm (not (p or q) => not p) ≔
begin
  assume p q;
  apply OR1;
  apply IMP4;
  apply AXM4
end;


symbol {|06.trace|} [p q] :
  Thm (not (p and (not p) or (q and not q))) ≔
begin
  assume p q;
  simplify;
  apply OR2
  {
    apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3
  }{
    apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3
  }
end;


symbol {|07.trace|} [p q] :
  Thm ((p or q) => (q or p)) ≔
begin
  assume p q;
  simplify;
  apply OR3
  {
    apply IMP4;
    apply OR4;
    apply AXM2
  }{
    apply IMP4;
    apply OR4;
    apply AXM4
  }
end;

symbol {|08.trace|} [p q] :
  Thm (not (p => q) => not q) ≔
begin
  assume p q;
  simplify;
  apply IMP1;
  apply IMP4;
  apply AXM7
end;



symbol {|09.trace|} [p] :
  Thm (not ((p or not p) => (p and not p))) ≔
begin
  assume p;
  apply IMP2
  {
    apply AND2;
    apply IMP4;
    apply NOT2;
    apply AXM3;
  }{
    apply OR4;
    apply AXM7;
  }
end;


symbol {|10.trace|} [p] :
  Thm (p => not p => not p) ≔
begin
  assume p;
  apply IMP3
  { apply AXM7 }
  { apply AXM7 }
end;

// TODO!
symbol {|11.trace|} [p] :
  Thm (p => (p => p and p)) ≔
begin
  assume p;
  apply IMP4;
  // apply IMP5;
  // apply AND4;
  // apply AXM3;
  // apply AXM3;
abort;

symbol {|12.trace|} [p q] :
  Thm (not (p <=> p) => q) ≔
begin
  assume p q;
  apply EQV1
  { apply IMP4; apply AXM2 }
  { apply IMP4; apply AXM1 }
end;

symbol {|13.trace|} [p] :
  Thm (not (p <=> not p)) ≔
begin
  assume p;
  apply EQV2
  {
    apply IMP4;
    apply NOT2;
    apply AXM3
  }
  {
    apply NOT1;
    apply AXM7
  }
end;

symbol {|14.trace|} [p q] :
  Thm ((p <=> not(p)) => q) ≔
begin
  assume p q;
  apply EQV3
  {
    apply IMP4;
    apply AXM2
  }
  {
    apply IMP4;
    apply NOT1;
    apply AXM1
  }
end;

symbol {|15.trace|} [p] :
  Thm (p <=> p) ≔
begin
  assume p;
  apply EQV4
  { apply AXM7 }
  { apply AXM7 }
end;

symbol {|16.trace|} [p q r] :
  Thm (not q => (p => (q => r))) ≔
begin
  assume p q r;
  apply IMP4;
  apply AXM5
end;

symbol {|17.trace|} [p q r] :
  Thm (q => (p => (not q => r))) ≔
begin
  assume p q r;
  apply IMP4;
  apply AXM6
end;

symbol {|18.trace|} [p] :
  Thm (
    ! ("a" ⋅) (
      (! ("x" ⋅) (not (VRAI and (var "x" = var "x"))))
    =>
      (var "a" = var "a" => p)
    )
  );
