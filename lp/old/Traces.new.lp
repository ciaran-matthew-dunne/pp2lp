require open pp2lp.Rules_new;

symbol {|01.trace|} (p q : El prd) :
  π ((not (p and q)) => ((not p) or (not q))) ≔
begin
  assume p q;
  apply AND1
  {
    print;
    apply IMP4;
    print;
    assume h;
    print;
    type OR4;
    apply OR4; print;
    apply AXM4; refine h; print;
  } {
    apply IMP4;
    assume h;
    apply OR4;
    apply NOT1;
    apply AXM1;
    refine h;
  };
end;

//  {
//    print;
//    apply IMP4;
//    print;
//    apply OR4;
//    apply AXM4
//  } {
//    apply IMP4;
//    apply OR4;
//    apply NOT1;
//    print;
//    apply AXM1
//  }
//end;
abort;
