require open pp2lp.Prelude;

opaque symbol {|26|} :
  π ((`!! a_t : Tuple (to_nat 2),
      let a ≔ (prj (to_nat 0) a_t) in
      let b ≔ (prj (to_nat 1) a_t) in
      a = b
      ⇒ (`!! x_t : Tuple (to_nat 2),
        let x ≔ (prj (to_nat 0) x_t) in
        let y ≔ (prj (to_nat 1) x_t) in
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
