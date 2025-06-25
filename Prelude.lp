require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;

// meta-level booleans
symbol bool : Set;
rule El bool ↪ Prop;

symbol TOP : Prf (⊤) ≔
  begin
    simplify;
    assume r h;
    refine h;
  end;

// lists
injective symbol list : Set → Set;
symbol nil [a : Set] : El (list a);
symbol ∷ [a : Set] : El (a ⤳ list a ⤳ list a);
notation ∷ infix right 5;

sequential symbol elem [a : Set] : El (a ⤳ list a ⤳ bool);
rule (elem _   nil)       ↪ ⊥
with (elem $x ($x ∷ _))   ↪ ⊤
with (elem $x (_  ∷ $ys)) ↪ (elem $x $ys);

symbol ≈ [a : Set] : El (a ⤳ a ⤳ bool);
notation ≈ infix right 5;

// identifiers
symbol String : TYPE;
builtin "String" ≔ String;

symbol idt : Set;
rule El idt ↪ String;

// variables, predicates, expressions, formulas
symbol vrb : Set ≔ list idt;
symbol prd : Set;
symbol exp : Set;
symbol frm : Set;

// sequents
symbol seq : Set;
injective symbol ⟝ : El (list prd ⤳ prd ⤳ seq);
notation ⟝ infix 0;

injective symbol ⟐  : El seq → TYPE;
injective symbol ✓ : El prd → TYPE;
rule (✓ $P) ↪ ⟐ (nil ⟝ $P);

// ???
symbol ⟿ : El (seq ⤳ prd ⤳ bool);
notation ⟿ infix 0;

symbol 𝕁 : El seq → El prd → TYPE;
