require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;

// setup for inductive types
builtin "Prop" ≔ Prop;
builtin "P" ≔ Prf;

// conditional type codes
symbol ⟹ : Prop → Set → Set;
notation ⟹ infix right 0;
rule El (⊤ ⟹ $x) ↪ El $x;

// -------------- old stuff -------------------

// meta-level booleans
symbol bool : Set;
rule El bool ↪ Prop;

symbol ite [a : Set] :
  El (bool ⤳ a ⤳ a ⤳ a);

rule ite ⊤ $x _ ↪ $x
with ite ⊥ _ $y ↪ $y;


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
symbol ⋅ [a : Set] (x : El a) ≔ cons x nil;
symbol ⨾ [a : Set] (x y : El a) ≔ cons x (cons y nil);
notation ∷ infix right 5;
notation ⋅ postfix 0;
notation ⨾ infix right 5;

symbol concat [a : Set] : El (list a ⤳ list a ⤳ list a);
rule concat nil $ys ↪ $ys
with concat (cons $x $xs) $ys ↪ cons $x (concat $xs $ys);

// `elem x xs` iff
sequential symbol elem [a : Set] : El (a ⤳ list a ⤳ bool);
rule (elem _   nil)         ↪ ⊥
with (elem $x (cons $x _))  ↪ ⊤
with (elem $x (cons _ $ys)) ↪ (elem $x $ys);

symbol ∈ [a : Set] ≔ elem [a];
notation ∈ infix 0;

// `replace x y zs` replaces the first instance of `x` in `xs` with `y`.
sequential symbol replace [a : Set] :
  El (a ⤳ a ⤳ list a ⤳ list a);

rule (replace  _ $y nil)          ↪ nil
with (replace $x $y ($x ∷ $zs))   ↪ $y ∷ $zs
with (replace $x $y ($z ∷ $zs))   ↪ $z ∷ (replace $x $y $zs);


// `nub xs` removes duplicate elements from `xs`.
symbol nub [a : Set] : El (list a ⤳ list a);
rule nub nil ↪ nil
with nub (cons $x $xs) ↪
  ite ($x ∈ $xs)
    (nub $xs)
    (cons $x (nub $xs));

// `union xs ys` returns the (set-theoretic) union of `xs` and `ys`.
symbol union [a : Set] (xs ys : El (list a)) ≔
  concat (nub xs) (nub ys);
