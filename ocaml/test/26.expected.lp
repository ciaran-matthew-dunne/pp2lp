require open pp2lp.B pp2lp.Int pp2lp.Rules;

opaque symbol {|26|} :
  π ((`!! a_t : Tuple 2,
      let a ≔ (prj 0 a_t) in
      let b ≔ (prj 1 a_t) in
      a = b
      ⇒ (`!! x_t : Tuple 2,
        let x ≔ (prj 0 x_t) in
        let y ≔ (prj 1 x_t) in
        x = y ⇒ x = a ⇒ y = b))) ≔
begin
  refine ALL8 _;
  assume _x1;
  assume _h2;
  try rewrite _h2;
  refine ALL8 _;
  assume _x3;
  assume _h4;
  try rewrite _h4;
  refine AXM7
end;
