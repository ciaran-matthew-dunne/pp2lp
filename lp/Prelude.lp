require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;

// meta-level booleans
symbol bool : Set;
symbol Bool ≔ El bool;
// ?? rule El bool ↪ Prop;

symbol ite [a : Set] : El (bool ⤳ a ⤳ a ⤳ a);
symbol true  : Bool;
symbol false : Bool;

rule ite true $x _ ↪ $x
with ite false _ $y ↪ $y;


// boolean disjunction
sequential symbol <> : El (bool ⤳ bool ⤳ bool);
notation <> infix 5;
rule (true <> _)      ↪ true
with (_ <> true)      ↪ true
with (false <> false) ↪ false;

// boolean conjunction
sequential symbol && : El (bool ⤳ bool ⤳ bool);
notation && infix 5;
rule (true && true) ↪ true
with (false && _)   ↪ false
with (_ && false)   ↪ false;

// boolean negation
sequential symbol !! : El (bool ⤳ bool);
rule (!! true) ↪ false
with (!! false) ↪ true;

// ------- lists ------------------------------------------
injective symbol 𝕃 : Set → TYPE;
injective symbol list : Set → Set;
rule El (list $X) ↪ 𝕃 $X;

injective symbol nil [a : Set] : 𝕃 a;
injective symbol cons [a : Set] : El a → 𝕃 a → 𝕃 a;

symbol ∷ [a] ≔ cons [a];
notation ∷ infix right 10;

sequential symbol concat [a : Set] : El (list a ⤳ list a ⤳ list a);
rule concat nil $ys ↪ $ys
with concat (cons $x $xs) $ys ↪ cons $x (concat $xs $ys);

sequential symbol elem [a : Set] : El (a ⤳ list a ⤳ bool);
rule (elem _   nil)         ↪ false
with (elem $x (cons $x _))  ↪ true
with (elem $x (cons _ $ys)) ↪ (elem $x $ys);

//sequential symbol reverse [a : Set] : El (list a ⤳ list a);
//rule (reverse nil)  ↪ nil
//with (reverse (cons $y $ys)) ↪ concat (reverse $ys) ($y) ;

symbol ⋿ [a : Set] ≔ elem [a];
notation ⋿ infix 0;

// `foreach p xs` rewrites to `true` iff `p` holds for each `x` in `xs`.
sequential symbol foreach [a : Set] :
  El ((a ⤳ bool) ⤳ list a ⤳ bool);
rule foreach $P nil ↪ true;
rule foreach $P (cons $x $xs) ↪ ($P $x) && foreach $P $xs;


// `replace x y zs` replaces the first instance of `x` in `xs` with `y`.
sequential symbol replace [a : Set] :
  El (a ⤳ a ⤳ list a ⤳ list a);

rule (replace  _ $y nil)             ↪ nil
with (replace $x $y (cons $x $zs))   ↪ cons $y $zs
with (replace $x $y (cons $z $zs))   ↪ cons $z (replace $x $y $zs);


// `nub xs` removes duplicate elements from `xs`.
symbol nub [a : Set] : El (list a ⤳ list a);
rule nub nil ↪ nil
with nub (cons $x $xs) ↪
  ite ($x ⋿ $xs)
    (nub $xs)
    (cons $x (nub $xs));

// `union xs ys` returns the (set-theoretic) union of `xs` and `ys`.
symbol union [a : Set] (xs ys : El (list a)) ≔
  concat (nub xs) (nub ys);


// ----- product types experiment ------------
injective symbol ℿ : Set → Set → TYPE;
symbol fst [X Y : Set] : (ℿ X Y) → El X;
symbol snd [X Y : Set] : (ℿ X Y) → El Y;

symbol × : Set → Set → Set;
notation × infix 20;

rule El ($X × $Y) ↪ ℿ $X $Y;
