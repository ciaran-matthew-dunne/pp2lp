require open Logic.U.Set Logic.U.Prop Logic.U.Arrow Logic.U.Quant;
require open pp2lp.Prelude;

// natural numbers
inductive ℕ : TYPE ≔
  | _0 : ℕ
  | +1 : ℕ → ℕ;
notation +1 postfix 100;

constant symbol nat : Set;
rule El nat ↪ ℕ;

symbol + : ℕ → ℕ → ℕ;
symbol - : ℕ → ℕ → ℕ;
symbol * : ℕ → ℕ → ℕ;

notation + infix left 20;
notation - infix left 20;
notation * infix left 30;

symbol _1 ≔ _0 +1;
symbol _2 ≔ _1 +1;
symbol _3 ≔ _2 +1;
symbol _4 ≔ _3 +1;
symbol _5 ≔ _4 +1;
symbol _6 ≔ _5 +1;
symbol _7 ≔ _6 +1;
symbol _8 ≔ _7 +1;
symbol _9 ≔ _8 +1;
symbol _10 ≔ _9 +1;

// enable parsing of natural numbers in decimal notation
builtin "0"  ≔ _0;
builtin "1" ≔ _1;
builtin "2" ≔ _2;
builtin "3" ≔ _3;
builtin "4" ≔ _4;
builtin "5" ≔ _5;
builtin "6" ≔ _6;
builtin "7" ≔ _7;
builtin "8" ≔ _8;
builtin "9" ≔ _9;
builtin "10" ≔ _10;

builtin "+" ≔ +;
builtin "*" ≔ *;
