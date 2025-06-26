require open Logic.U.Set Logic.U.Prop Logic.U.Arrow Logic.U.Quant;
require open pp2lp.Prelude;

// primitive logical symbols
injective symbol and : El (prd ⤳ prd ⤳ prd);
injective symbol or : El (prd ⤳ prd ⤳ prd);
injective symbol => : El (prd ⤳ prd ⤳ prd);
injective symbol <=> : El (prd ⤳ prd ⤳ prd);
injective symbol not : El (prd ⤳ prd);
injective symbol ! : El ((exp ⤳ prd) ⤳ prd);
injective symbol # : El ((exp ⤳ prd) ⤳ prd);
injective symbol =  : El (exp ⤳ exp ⤳ prd);
injective symbol != : El (exp ⤳ exp ⤳ prd);
injective symbol Ⅎ : El frm → El prd;

symbol VRAI  : El prd;
symbol FAUX : El prd;

notation = infix left 2;
notation != infix left 2;

notation and infix left 2;
notation or  infix left 2;
notation =>  infix left 2;
notation <=> infix left 1;
notation not       prefix 3;

notation ! quantifier;
notation # quantifier;

// weird quantifiers (?)
symbol ♢ : El ((exp ⤳ prd) ⤳ prd);
symbol ♡ : El ((exp ⤳ prd) ⤳ prd);

notation ♢ quantifier;
notation ♡ quantifier;

// syntactic equality on predicates
rule FAUX ≈ FAUX ↪ ⊤
with VRAI ≈ VRAI ↪ ⊤
with ($p1 and $p2) ≈ ($q1 and $q2) ↪ ($p1 ≈ $q1) ∧ ($p2 ≈ $q2)
with ($p1 or $p2) ≈ ($q1 or $q2)   ↪ ($p1 ≈ $q1) ∧ ($p2 ≈ $q2)
with ($p1 => $p2) ≈ ($q1 => $q2)   ↪ ($p1 ≈ $q1) ∧ ($p2 ≈ $q2)
with ($p1 <=> $p2) ≈ ($q1 <=> $q2) ↪ ($p1 ≈ $q1) ∧ ($p2 ≈ $q2)
with ($e1 = $e2) ≈ ($f1 = $f2)   ↪ ($e1 ≈ $f1) ∧ ($e2 ≈ $f2)
with ($e1 != $e2) ≈ ($f1 != $f2) ↪ ($e1 ≈ $f1) ∧ ($e2 ≈ $f2)
with (! $P) ≈ (! $Q) ↪ (`∀ x, ($P x ≈ $Q x))
with (# $P) ≈ (# $Q) ↪ (`∀ x, ($P x ≈ $Q x))
with (♢ $P) ≈ (♢ $Q) ↪ (`∀ x, ($P x ≈ $Q x))
with (♡ $P) ≈ (♡ $Q) ↪ (`∀ x, ($P x ≈ $Q x));



// arithmetic
symbol ≤ : El (exp ⤳ exp ⤳ prd);
symbol < : El (exp ⤳ exp ⤳ prd);
symbol ≪ : El (exp ⤳ exp ⤳ prd);
symbol 𝟎 : El (exp);
symbol 𝟏 : El (exp);
symbol ⨪ : El (exp ⤳ exp);
symbol + : El (exp ⤳ exp ⤳ exp);
symbol - : El (exp ⤳ exp ⤳ exp);
symbol ℕ : El exp;
symbol ∈ : El (exp ⤳ exp ⤳ prd);
symbol solveur [a : Set] : El (a ⤳ a);

notation ≤ infix 5;
notation < infix 5;
notation < infix 5;
notation + infix 5;
notation - infix 5;
notation ∈ infix 5;

// ordered pairs, set equality ??
symbol opair : El (exp ⤳ exp ⤳ exp);
symbol eql_set : El (exp ⤳ exp ⤳ prd);

symbol ⭆ : El (list prd ⤳ prd ⤳ prd);
notation ⭆ infix 5;

rule (nil ⭆ $p) ↪ $p
with (($q ∷ $qs) ⭆ $p) ↪ $q => ($qs ⭆ $p);
