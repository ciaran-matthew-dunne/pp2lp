require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax pp2lp.Rules;

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


symbol {|18.trace|} [p : El frm] :

  Thm (
    ! ("a" ⋅) (
      (! ("x" ⋅) (not (VRAI and ("x" = "x"))))
    =>
      ("a" = "a" => p)
    )
  ) ≔
begin
  assume p;
  apply ALL8;
  apply ALL7 {
    apply AND2_1;
    apply VR3_1;
    apply EVR2_1;
    apply STOP_1;
  } {
    apply NRM1;
    apply FX3;
    print;
  };
end;

//symbol {|19.trace|} [q : El prd] :
//  Thm (
//    ! ("a" ⋅) (
//      (
//        (! ("x" ⋅) (not (VRAI and ((var "p") ‵ (var "x")))))
//      and
//        (! ("x4" ⋅) (
//          (# ("x5" ⋅) ((var "x4" ⨾ var "x5") ∈ (var "p")))
//        =>
//          ((var "x4" ⨾ ((var "p") ‶ (var "x4"))) ∈ (var "p"))
//        ))
//      )
//    =>
//      (
//        ((var "p") ‵ (var "a")) => q
//      )
//    )
//  ) ≔
//begin
//  assume q;
//  simplify;
//  apply ALL8;
//  apply AND3;
//  apply ALL7 {
//    apply AND2_1;
//    apply VR3_1;
//    apply STOP_1;
//  } {
//    apply NRM14;
//    apply ALL9;
//    print;
//    apply ALL7 {
//      apply XST7_1;
//      apply ALL8_1;
//      apply IMP4_1;
//      apply STOP_1;
//    } {
//      simplify;print;
//      apply NRM8;
//      apply NRM13;
//      apply ALL9;
//      // AXM9 really needs guidance...
//      apply AXM9 [_] [var "p" ‵ var "x"] [_] [_] ["x"] [var "a"];
//    };
//  };
//end;

symbol {|20.trace|} [p] :
  Thm (
    not (! ("x" ⋅) (! ("y" ⋅) (var "x" = var "y")))
  =>
    (p or (not p))
  ) ≔
begin
  assume p;
  apply ALL1;
  apply ALL5;
  apply ALL8;
  apply IMP4;
  apply OR4;
  apply AXM7;
end;


symbol {|21.trace|} [p q : El frm] :
Thm (
    ! ("x" ⋅) (! ("y" ⋅) (q ‵ "x" ‵ "y"))
  and
    ! ("x6" ⨾ "x5") (
      # ("x7" ⋅) ("x7" = q ‵ "x6" ‵ "x5")
    =>
      (q ‵ "x6" ‵ "x5" = q ‵ "x6" ‵ "x5")
    )
  =>
      (p or (not p))
  ) ≔
begin
  assume p q;
  apply AND3;
  apply ALL7 { // (1)
    apply STOP_1;
  } {
    apply NRM15;
    print;
    apply ALL9;
    print;
    apply ALL7 { // (3)
      apply XST7_1; // (2)
      apply ALL8_1; // (3)
      apply IMP4_1;
      apply STOP_1;
    } {
      print;
      apply NRM8; // (2)
      apply NRM13;
      apply ALL9;
      apply OR4;
      apply AXM7;
    }
  }
end;

symbol {|22.trace|} : Thm (
  not (! ("x" ⋅) (! ("y" ⋅ ) (not ("x" = "x"))))
) ≔
begin
  apply ALL2;
  apply ALL6;
  print;
  apply ALL7 {
    apply EVR2_1;
    apply STOP_1;
  } {
    apply NRM1;
    apply AXM7;
  }
end;

symbol {|23.trace|} [p : El frm] :
  Thm (
    ! ("a" ⨾ "b") (
      not (# ("x" ⋅) (# ("y" ⋅) (p ‵ "x" ‵ "y")))
    and
      ! ("x6" ⨾ "x5") (
        # ("x7" ⋅) ("x7" = p ‵ "x6" ‵ "x5")
      =>
        (p ‵ "x6" ‵ "x5" = p ‵ "x6" ‵ "x5")
      )
    =>
      not (p ‵ "a" ‵ "b")
    )
  ) ≔
begin
  assume p;
  apply ALL8;
  apply AND3;
  apply XST1;
  apply XST5;
  apply ALL7 {
    apply STOP_1
  } {
    apply NRM14;
    apply ALL9;
    apply ALL7 {
      apply XST7_1;
      apply ALL8_1;
      apply IMP4_1;
      apply STOP_1;
    } {
      apply NRM8;
      apply NRM13;
      apply ALL9;
      apply STOP;
      apply NOT1;
      print;
      compute
        multisubst ("x" ⨾ "y") (cons (var "a") (cons (var "b") nil))
        Φ (p ‵ "a" ‵ "b");
      apply AXM9 [_]
        [Φ (p ‵ "x" ‵ "y")] [FAUX] [Φ (p ‵ "a" ‵ "b")] // P, Q, R : El prd
        [("x" ⨾ "y")] [cons (var "a") (cons (var "b") nil)] // xs : El vrb, es : El (list exp);
    };
  };
end;
