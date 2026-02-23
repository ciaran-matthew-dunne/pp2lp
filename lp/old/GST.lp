require open Logic.U.Arrow Logic.U.Prop;

// raw type constructor for cartesian product.
injective symbol ℿ : Set → Set → TYPE;
symbol fst [X Y : Set] : (ℿ X Y) → El X;
symbol snd [X Y : Set] : (ℿ X Y) → El Y;

// infix set-code constructor for cartesian product.
symbol × : Set → Set → Set;
notation × infix 20;
rule El ($X × $Y) ↪ ℿ $X $Y;

builtin "Prop" ≔ Prop;
builtin "P" ≔ Prf;

symbol v : Set;
symbol i : Set;

symbol Cat : TYPE;
symbol Obj : Cat → TYPE;
symbol Arr [C : Cat] : Obj C → Obj C → TYPE;
//symbol hd [C X Y] : Arr X Y → Obj C;
//symbol tl [C : Cat] : Arr C → Obj C;


symbol SET : Cat;
rule Obj SET ↪ Set
with Arr SET ↪ (Set → Set)
with hd [SET] $f ↪   ;

symbol functor (a b : Set) ≔
  El (a ⤳ b) + El (());

symbol fmap [a b]
  (F : Set → Set) (fmap : ) : Set → Set;

symbol coalgebra : (Set → Set) → TYPE;
symbol

symbol apg  : Set → Set → TYPE;
symbol elts : apg i v → TYPE;

symbol ∅ : apg i v;
rule elts ∅ ↪ (El i → El v);


symbol root : apg → El v;




symbol Ω : apg;
rule (elts Ω) ↪ (λ _, Ω);


type Ω;
compute elts Ω;

symbol crop : apg → El v → apg;

//injective symbol splice [v : Set] : apg v → (El v → apg v) → apg v;
