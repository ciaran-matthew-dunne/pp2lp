require open pp2lp.Syntax;

// --- production rules -------------
symbol STOP_1 [H : El (list prd)] [P : El prd] :
  Res (H ⟝ P);
rule obtain (STOP_1 [_] [$P]) ↪ $P;

symbol EVR2_1 [H : El (list prd)] [X : El exp] :
  Res (H ⟝ FAUX) →
  Res (H ⟝ not (X = X));
rule obtain (EVR2_1 $t) ↪ obtain $t;

symbol VR3_1 [H : El (list prd)] [R : Prd] :
  Res (H ⟝ R) →
  Res (H ⟝ VRAI => R);
rule obtain (VR3_1 $t) ↪ obtain $t;

symbol AND2_1 [H : El (list prd)] [P Q : Prd] :
  Res (H ⟝ P => not Q) →
  Res (H ⟝ not (P and Q));
rule obtain (AND2_1 $t) ↪ obtain $t;


// ---- inference rules ------------------
symbol ALL2 [H : El (list prd)] [x y : El str] [P : El prd] :
  If (x !== y) (
    (H ⊩ not (! (x ⨾ y) P)) ⤳
    (H ⊩ not (! (x ⋅) (! (y ⋅) P)))
  );

symbol ALL6 [H : El (list prd)] [P : El prd] [xs : El vrb] :
  El (
    (H ⊩ ! xs P => FAUX) ⤳
    (H ⊩ not (! xs P))
  );

symbol ALL7 [H : El (list prd)] [P Q : El prd] [xs : El vrb] :
  Π R : Res (H ⟝ P), El (
    (H ⊩ (♢ xs R) => Q) ⤳
    (H ⊩ (! xs P) => Q)
  );

symbol ALL8 [H : El (list prd)] [P : El prd] [xs : El vrb] :
  El (
    (H ⊩ P) ⤳
    (H ⊩ ! xs P)
  );

symbol NRM1 [H : El (list prd)] [P S : El prd] [xs : El vrb] :
  El (
    (H ⊩ P => S) ⤳
    (H ⊩ (♢ xs P) => S)
  );

symbol AXM7 [H : El (list prd)] [P : El prd] :
  El (
    H ⊩ P => P
  );

symbol FX3 [H : El (list prd)] [R : El prd] :
  El (
    H ⊩ FAUX => R
  );

symbol {|18.trace|} [p : El prd] :
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
  apply ALL7
  {
    apply AND2_1;
    apply VR3_1;
    apply EVR2_1;
    apply STOP_1;
  }
  {
    apply NRM1;
    apply FX3;
  };
end;

type ALL7 _ _;

type AXM7;
type NRM1;
type NRM1 (AXM7);

type STOP_1;
type EVR2_1;
type EVR2_1 (STOP_1);

//type ALL7;
type ALL7 (EVR2_1 (STOP_1)) (NRM1 (AXM7));

type ALL6 (ALL7 (EVR2_1 (STOP_1)) (NRM1 (AXM7)));
type ALL2;

assert
  ⊢ ALL2 (ALL6 (ALL7 (EVR2_1 (STOP_1)) (NRM1 (AXM7))))
  : Thm (not (! ("x" ⋅) (! ("y" ⋅) (not ("x" = "x")))));
