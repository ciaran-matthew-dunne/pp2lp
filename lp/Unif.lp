require open Logic.U.Arrow;

symbol bool : Set;
symbol true  : El bool;
symbol false : El bool;

// lists
injective symbol list : Set → Set;
injective symbol nil [a : Set] : El (list a);
injective symbol cons [a : Set] : El (a ⤳ list a ⤳ list a);

sequential symbol elem [a : Set] : El (a ⤳ list a ⤳ bool);
rule (elem _   nil)         ↪ false
with (elem $x (cons $x _))  ↪ true
with (elem $x (cons _ $ys)) ↪ (elem $x $ys);

symbol prd  : Set;
symbol seq  : Set;
symbol exp : Set;
symbol vrb : Set;

injective symbol and  : El (prd ⤳ prd ⤳ prd);
injective symbol or   : El (prd ⤳ prd ⤳ prd);
injective symbol =>   : El (prd ⤳ prd ⤳ prd);
injective symbol <=>  : El (prd ⤳ prd ⤳ prd);
injective symbol not  : El (prd ⤳ prd);
injective symbol =    : El (exp ⤳ exp ⤳ prd);
injective symbol ! : El (vrb ⤳ prd ⤳ prd);
injective symbol # : El (vrb ⤳ prd ⤳ prd);
//injective symbol atom : El (frm ⤳ prd);
//injective symbol var : El (str ⤳ exp);

notation =   infix left 2;
notation and infix left 2;
notation or  infix left 2;
notation =>  infix left 2;
notation <=> infix left 1;
notation not prefix 3;

// constructor for sequents
injective symbol ⟝ : El (list prd ⤳ prd ⤳ seq);
notation ⟝ infix 0;

// set-codes for sequent deriviations
injective symbol drv : El seq → Set;

// boolean-guarded `El`.
symbol If : El bool → Set → TYPE;
// rewrite rule to avoid manually 'proving' boolean computations in side-conditions.
rule If true $X ↪ El $X;

// an inference rule with no premises and a side-condition.
symbol AXM1 [H : El (list prd)] [P Q : El prd] :
  If (elem (not P) H) (
    drv (H ⟝ P => Q)
  );

// an example of where this style fails.
symbol prf_oops [P Q] :
  El (drv (cons (not P) nil ⟝ P => Q)) ≔
begin
  assume P Q;
  try apply AXM1; //apply gets stuck here because it cannot unify:
  //  El (▷ (cons (not P) nil ⟝ (P => Q)))
  //  ≡ If (elem (not ?16) ?15) (▷ (?15 ⟝ (?16 => ?17)))
abort;

// but we can give the unifier a good strategy.
// and now the proof will go through.
//-----------------------------------------
  //unif_rule El (▷ $Σ) ≡ (If $b (▷ $Σ'))
  //  ↪ [$Σ ≡ $Σ'; $b ≡ $true];

  //symbol prf_qed [P Q] :
  //  El (▷ (cons (not P) nil ⟝ P => Q)) ≔
  //begin
  //  assume P Q;
  //  apply AXM1;
  //end;
//-----------------------------------------

// this approach fails when we have rules with (deriviation) premises
// and side conditions. `apply` can't figure out the right term to
// refine the proof state with.

// a better approach is 'conditional derivation types' at the 'top-level':
injective symbol ✓ : El bool → El seq → TYPE;
// and defining 'normal' deriviation as a special case.
symbol ▷ : El seq → TYPE;
rule (▷ $Σ) ↪ ✓ true $Σ;

symbol AXM1' [H : El (list prd)] [P Q : El prd] :
  ✓ (elem (not P) H) (H ⟝ P => Q);

symbol prf_qed [P Q] :
  ▷ ((cons (not P) nil) ⟝ P => Q)
≔ begin
    assume P Q;
    print;
    // ?11 : ▷ (cons (not P) nil ⟝ (P => Q))
    apply AXM1' // suceeds because:
    // ?11 : ✓ true (cons (not P) nil ⟝ (P => Q))
    // can easily unify with
    // AXM1' : ✓ (elem (not P) H) (H ⟝ P => Q);
  //
end;
