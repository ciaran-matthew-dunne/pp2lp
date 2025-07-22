require open pp2lp.Syntax;

coerce_rule coerce String Exp $x ↪ VAR $x;
assert ⊢ ("x" = "x") : Prd;

symbol ALL2 [H : El (list prd)] [x y : El idt] [P : El prd] :
  If (x !== y) (
    (H ⊩ not (! (x ⨾ y) P)) ⤳
    (H ⊩ not (! (x ⋅) (! (y ⋅) P)))
  );

symbol ALL6 [H : El (list prd)] [P : El prd] [xs : El vrb] :
  El (
    (H ⊩ ! xs P => FAUX) ⤳
    (H ⊩ not (! xs P))
  );

symbol STOP_1 [H : El (list prd)] [P : El prd] : Res (H ⟝ P);
rule obtain (STOP_1 [_] [$P]) ↪ $P;

symbol EVR2_1 [H : El (list prd)] [X : El exp] :
  Res (H ⟝ FAUX) →
  Res (H ⟝ not (X = X));

rule obtain (EVR2_1 $Θ) ↪ obtain $Θ;

symbol ALL7 [H : El (list prd)] [P Q : El prd] [xs : El vrb] :
  Π R : Res (H ⟝ P), El (
    (H ⊩ (♢ xs R) => Q) ⤳
    (H ⊩ (! xs P) => Q)
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

symbol trace : Thm (not (! ("x" ⋅) (! ("y" ⋅) (not ("x" = "x"))))) ≔
begin
  apply ALL2;
  apply ALL6;
  apply ALL7
  {
    apply EVR2_1;
    apply STOP_1;
  }
  {
    apply NRM1;
    apply AXM7;
  }
end;
