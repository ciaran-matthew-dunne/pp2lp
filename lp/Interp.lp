require open pp2lp.Prelude pp2lp.Syntax;

symbol ⇔ : Prop → Prop → Prop;
notation ⇔ infix 0;

// typecode for individuals
symbol ι : Set;
symbol = [a : Set] : El (a ⤳ a ⤳ bool);
notation = infix 0;

injective symbol ∗ : Set → Set → Set; // product types
notation ∗ infix right 20;

injective symbol pair [a b : Set] : El (a ⤳ b ⤳ a ∗ b);
symbol fst [a b : Set] : El (a ∗ b ⤳ a);
symbol snd [a b : Set] : El (a ∗ b ⤳ b);

rule fst (pair $a _) ↪ $a;
rule snd (pair _ $b) ↪ $b;

symbol map (k v : Set) ≔ list (k ∗ v);

sequential symbol lookup [k v : Set] : El (k ⤳ map k v ⤳ v);
rule lookup $x (cons (pair $x $y) $ys) ↪ $y
with lookup $x (cons (pair _  _ ) $ys) ↪ lookup $x $ys;

symbol interp [a b : Set] : El (map idt ι ⤳ a ⤳ b);

rule interp [_] [bool] $m (AND $P $Q)  ↪ (interp $m $P) ∧ (interp $m $Q)
with interp [_] [bool] $m (OR  $P $Q)  ↪ (interp $m $P) ∨ (interp $m $Q)
with interp [_] [bool] $m (IMPL $P $Q) ↪ (interp $m $P) ⇒ (interp $m $Q)
with interp [_] [bool] $m (IFF $P $Q)  ↪ (interp $m $P) ⇔ (interp $m $Q)
with interp [_] [bool] $m (NOT $P)     ↪ ¬ (interp $m $P)
with interp [_] [bool] $m (VRAI)       ↪ ⊤
with interp [_] [bool] $m (FAUX)       ↪ ⊥;

rule interp [_] [bool] $m (EQ $X $Y)
  ↪ (interp [_] [ι] $m $X) = (interp $m $Y)

with interp [_] [bool] $m (ATOM $Φ)  ↪ interp $m $Φ
with interp [_] [ι]    $m (VAR $x)   ↪ lookup $x $m;

// universal quantification
rule interp $m (ALL nil $P) ↪ interp $m $P
with interp [_] [bool] $m (ALL (cons $v $vs) $P)
  ↪ `∀ x, interp (cons (pair $v x) $m) (ALL $vs $P);

// existential quantification
rule interp $m (EXI nil $P) ↪ interp $m $P
with interp [_] [bool] $m (EXI (cons $v $vs) $P)
  ↪ `∃ x, interp (cons (pair $v x) $m) (EXI $vs $P);

// sequents
rule interp [seq] [bool] $m (nil ⟝ $P) ↪ interp $m $P
with interp [seq] [bool] $m (cons $P $H ⟝ $Q)
   ↪ interp $m $P ⇒ interp [seq] [bool] $m ($H ⟝ $Q);

// derivations
rule El (▷ $Σ) ↪ Prf (interp [seq] [bool] nil $Σ);

symbol foo ≔ ALL ("x" ⨾ "y") (FAUX);
compute interp [prd] [bool] nil foo;

symbol prf : El (▷ (nil ⟝ VRAI and VRAI));
compute El (▷ (nil ⟝ VRAI and VRAI));
