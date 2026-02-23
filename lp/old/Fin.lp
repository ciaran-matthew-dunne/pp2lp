require open pp2lp.Rules;




symbol str_eq [x y : El str] : Prf (¬(x == y));


symbol trace :▷ (nil ⟝ not (! ("x" ⋅) (! ("y" ⋅) (not (VAR "x" = VAR "x")))))
  ≔  ALL2 (ALL6 (ALL7 (EVR2_1 (STOP_1)) (NRM1 (AXM7))));

//begin
//  apply ALL2;
//  apply ALL6;
//  apply ALL7 (EVR2_1 (STOP_1));
//  } {
//    apply NRM1;
//    apply AXM7;
//  };
//end;


symbol sch : Set;
symbol mksch : El (string ⤳ bool ⤳ list seq ⤳ seq ⤳ sch);
symbol mkrule : El sch → Set;

symbol findrule [a : Set] : El string → Set;
rule findrule "AXM7" ↪ mkrule ;

symbol arity : El sch → Nat;
rule arity (mksch _ $xs _) ↪ length $xs;


rule mkrule (mksch $P $xs $x) ↪
  If $P ($xs ⤳ $x)
