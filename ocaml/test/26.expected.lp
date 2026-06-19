require open pp2lp.Prelude;

opaque symbol {|26|} :
  π ((`!! a_t : Tuple 2,
      (a_t ⋕ 0) = (a_t ⋕ 1)
      ⇒ (`!! x_t : Tuple 2,
        (x_t ⋕ 0) = (x_t ⋕ 1)
        ⇒ (x_t ⋕ 0) = (a_t ⋕ 0) ⇒ (x_t ⋕ 1) = (a_t ⋕ 1)))) ≔
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
