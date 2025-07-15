require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;

// meta-level booleans
symbol bool : Set;
rule El bool ↪ Prop;

builtin "Prop" ≔ Prop;
builtin "P" ≔ Prf;

// strings
symbol String : TYPE;
builtin "String" ≔ String;

constant symbol string : Set;
rule El string ↪ String;


// lists
injective symbol list : Set → Set;
injective symbol nil [a : Set] : El (list a);
injective symbol cons [a : Set] : El (a ⤳ list a ⤳ list a);

symbol ∷ [a : Set] ≔ cons [a];
notation ∷ infix right 5;

sequential symbol elem [a : Set] : El (a ⤳ list a ⤳ bool);
rule (elem _   nil)       ↪ ⊥
with (elem $x ($x ∷ _))   ↪ ⊤
with (elem $x (_  ∷ $ys)) ↪ (elem $x $ys);

symbol ∈ [a : Set] ≔ elem [a];
notation ∈ infix 0;

// `replace x y zs` replaces the first instance of `x` in `xs` with `y`.
sequential symbol replace [a : Set] :
  El (a ⤳ a ⤳ list a ⤳ list a);

rule (replace  _ $y nil)          ↪ nil
with (replace $x $y ($x ∷ $zs))   ↪ $y ∷ $zs
with (replace $x $y ($z ∷ $zs))   ↪ $z ∷ (replace $x $y $zs);

symbol ≣ [a : Set] : El (a ⤳ a ⤳ bool);
notation ≣ infix right 5;
