require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

symbol ⭆ : El (list prd ⤳ prd ⤳ prd);
notation ⭆ infix 5;

rule (nil ⭆ $p) ↪ $p
with (($q ∷ $qs) ⭆ $p) ↪ $q => ($qs ⭆ $p);

// ----------------------------------------------
// 5.11 INS rule
// ----------------------------------------------
symbol INS [H Q : El (list prd)] :
  ⟐ (H ⟝ Q ⭆ FAUX) →
  ⟐ (H ⟝ FAUX);
