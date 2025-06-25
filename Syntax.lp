require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
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

notation = infix left 2;
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

// booleans
symbol VRAI  : El prd;
symbol FAUX : El prd;
