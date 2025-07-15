require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax pp2lp.Rules;

injective symbol ✓ : El prd → TYPE;
// theorem, derivable sequent with no hypothesis.
rule (✓ $P) ↪ ⟐ (nil ⟝ $P);




symbol {|05.trace|} [p q] :
  ✓ (not (p or q) => not p) ≔
begin
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

symbol {|11.trace|} [p] :
  ✓ (p => (p => p and p)) ≔
begin
  assume p;
  simplify;
  apply IMP4;

  // apply IMP5 (1);
  // apply AND4;
  // apply AXM3;
  // apply AXM3;
abort;

symbol {|12.trace|} [p q] :
  ✓ (not (p <=> p) => q) ≔
begin
  assume p q;
  simplify;
  apply EQV1 {
    apply IMP4;
    apply AXM2;
    simplify elem;
    refine TOP;
  }{
    apply IMP4;
    apply AXM1;
    simplify elem;
    refine TOP;
  };
end;

symbol {|13.trace|} [p] :
  ✓ (not (p <=> not p)) ≔
begin
  assume p;
  simplify;
  apply EQV2 {
    apply IMP4;
    apply NOT2;
    apply AXM3;
    simplify elem;
    refine TOP;
  } {
    apply NOT1;
    apply AXM7;
  };
end;

symbol {|14.trace|} [p q] :
  ✓ ((p <=> not(p)) => q) ≔
begin
  assume p q;
  simplify;
  apply EQV3 {
    apply IMP4;
    apply AXM2;
    simplify elem;
    refine TOP;
  } {
    apply IMP4;
    apply NOT1;
    apply AXM1;
    simplify elem;
    refine TOP;
  };
end;

symbol {|15.trace|} [p] :
  ✓ (p <=> p) ≔
begin
  assume p;
  simplify;
  apply EQV4
    { apply AXM7 }
    { apply AXM7 };
end;

symbol {|16.trace|} [p q r] :
  ✓ (not q => (p => (q => r))) ≔
begin
  assume p q r;
  simplify;
  apply IMP4;
  apply AXM5;
  simplify elem;
  refine TOP;
end;

symbol {|17.trace|} [p q r] :
  ✓ (q => (p => (not q => r))) ≔
begin
  assume p q r;
  simplify;
  apply IMP4;
  apply AXM6;
  simplify elem;
  refine TOP;
end;

symbol {|18.trace|} [p] :
  ✓ (
    ! (one "a") (
      ! (one "x") (not (VRAI and (var "x" = var "x")))
    =>
      (var "a" = var "a" => p)
    )
  ) ≔
begin
  assume p;
  simplify;

  apply ALL8;
  //apply ALL7 VRAI;
  apply ALL7 VRAI
    { simplify;
      admit
    }
    { apply NRM1;
      apply FX3;
    };

  type STOP';
  type STOP _ ;
  type EVR2;
  type VR3;
  type AND2;
abort;


type VR3;
type EVR2;

type STOP';



type FX3;


symbol {|19.trace|} [p q r] :
  ✓ (not q => (p => (q => r))) ≔
begin
  assume p q r;
  simplify;
  apply IMP4;
  apply AXM5;
  simplify elem;
  refine TOP;
end;

symbol foo : El (exp ⤳ prd);


symbol p1 : ✓ (FAUX => FAUX) ≔ AXM7;



symbol {|22.trace|} :
  ✓ (not (! (one "x") (! (one "y") (not (var "x" = var "x"))))) ≔
begin
abort;

symbol {|26.trace|} :
✓ (! (two "a" "b")
    ((var "a" = var "b")
  =>
    (! (one "x") (
      ! (one "y") (
        (var "x" = var "y") => ((var "x" = var "a") => (var "y" = var "b"))
      )
    ))
  )) ≔
begin
  simplify;
  apply ALL8;
  apply OPR1;
  apply ALL4;
abort;


//symbol {|20.trace|} [p ] :
//  ✓ (not (`! x,`! y, x = y) => (p or not p)) ≔
//begin
//  assume p;
//  simplify;
//  apply ALL1;
//  apply ALL5;
//  apply ALL8;
//  //apply AXM5;
//  //simplify elem;
//  //refine TOP;
//end;
