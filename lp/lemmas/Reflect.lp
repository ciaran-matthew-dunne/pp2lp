// lemmas/Reflect.lp — reflective decision procedure for ℤ-linear equalities,
// with scalar coefficients (k·x).  The emitter discharges a generated arithmetic
// equality `e1 = e2` (τ ι) by reflecting onto `to_int` (Stdlib.Z) via [toint_eq]
// (lemmas/Int.lp) and proving the residual ℤ equality reflectively: reify each
// side to an [LE] over an environment ρ of the distinct atoms, COMPUTE a canonical
// coefficient-monomial [NF], close with `eq_refl` when they agree.  Coefficients
// (from `prod(k,x)` and combination) are true ℤ scalars; the combine/scale
// soundness rests on the ℤ ring laws in [lemmas/Zmul.lp].
require open pp2lp.B;
require open pp2lp.lemmas.Int;
require open pp2lp.lemmas.Zmul;
require open Stdlib.List;
require Stdlib.Nat;
// reified linear expr with scalar multiplication
inductive LE : TYPE ≔
  | Lvar : ℕ → LE
  | Llit : ℤ → LE
  | Ladd : LE → LE → LE
  | Lneg : LE → LE
  | Lmul : ℤ → LE → LE;

symbol den : 𝕃 int → LE → ℤ;
rule den $ρ (Lvar $i) ↪ nth Z0 $ρ $i
with den _  (Llit $z) ↪ $z
with den $ρ (Ladd $a $b) ↪ den $ρ $a + den $ρ $b
with den $ρ (Lneg $a) ↪ — (den $ρ $a)
with den $ρ (Lmul $c $a) ↪ $c * den $ρ $a;

// monomial list (coeff, index), sorted by index ascending, combined, nonzero coeffs
inductive ML : TYPE ≔ | mnil : ML | mcons : ℤ → ℕ → ML → ML;
symbol mlcode : Set; rule τ mlcode ↪ ML;
inductive NF : TYPE ≔ | mkNF : ML → ℤ → NF;
symbol nfcode : Set; rule τ nfcode ↪ NF;

symbol sumML : 𝕃 int → ML → ℤ;
rule sumML _  mnil           ↪ Z0
with sumML $ρ (mcons $c $i $r) ↪ $c * nth Z0 $ρ $i + sumML $ρ $r;

symbol denNF : 𝕃 int → NF → ℤ;
rule denNF $ρ (mkNF $ml $k) ↪ sumML $ρ $ml + $k;

symbol nlt : ℕ → ℕ → 𝔹;   // ℕ < (own; avoids clashes)
rule nlt _ _0 ↪ false
with nlt _0 (_ +1) ↪ true
with nlt ($x +1) ($y +1) ↪ nlt $x $y;

// insert (c, i): combine same index (drop if 0), else sort by index
symbol minsert : ℤ → ℕ → ML → ML;
rule minsert $c $i mnil ↪ if (isZ0 $c) mnil (mcons $c $i mnil)
with minsert $c $i (mcons $c' $j $r) ↪
  if (Stdlib.Nat.eqn $i $j)
     (if (isZ0 ($c + $c')) $r (mcons ($c + $c') $i $r))
     (if (nlt $i $j) (mcons $c $i (mcons $c' $j $r)) (mcons $c' $j (minsert $c $i $r)));

symbol maddML : ML → ML → ML;
rule maddML mnil $l ↪ $l
with maddML (mcons $c $i $r) $l ↪ minsert $c $i (maddML $r $l);

symbol mscaleML : ℤ → ML → ML;
rule mscaleML _ mnil ↪ mnil
with mscaleML $c (mcons $c' $i $r) ↪
  if (isZ0 ($c * $c')) (mscaleML $c $r) (mcons ($c * $c') $i (mscaleML $c $r));

symbol addNF : NF → NF → NF;
rule addNF (mkNF $l1 $k1) (mkNF $l2 $k2) ↪ mkNF (maddML $l1 $l2) ($k1 + $k2);
symbol mulNF : ℤ → NF → NF;
rule mulNF $c (mkNF $l $k) ↪ mkNF (mscaleML $c $l) ($c * $k);

symbol norm : LE → NF;
rule norm (Lvar $i) ↪ mkNF (mcons (Zpos H) $i mnil) Z0
with norm (Llit $z) ↪ mkNF mnil $z
with norm (Ladd $a $b) ↪ addNF (norm $a) (norm $b)
with norm (Lneg $a) ↪ mulNF (Zneg H) (norm $a)
with norm (Lmul $c $a) ↪ mulNF $c (norm $a);

// ============ soundness ============

opaque symbol isZ0_eq : Π c, π (isZ0 c = true) → π (c = Z0) ≔
begin
  induction
  { assume h; reflexivity }
  { assume p h; refine ⊥ₑ (false≠true h) }
  { assume p h; refine ⊥ₑ (false≠true h) }
end;

// (a+b)+(c+d) = (a+c)+(b+d) on ℤ (reuse pattern)
opaque symbol zadd4 a b c d : π ((a + b) + (c + d) = (a + c) + (b + d)) ≔
begin assume a b c d;
  rewrite +_assoc; rewrite left +_assoc b c d; rewrite (+_com b c);
  rewrite +_assoc c b d; rewrite left +_assoc a c (b + d); reflexivity end;

opaque symbol minsert_sound (ρ : 𝕃 int) (c : ℤ) (i : ℕ) :
  Π ml, π (sumML ρ (minsert c i ml) = c * nth Z0 ρ i + sumML ρ ml) ≔
begin
  assume ρ c i;
  induction
  { // mnil: if (isZ0 c) mnil (mcons c i mnil)
    refine ind_𝔹_eq (λ b, sumML ρ (if b mnil (mcons c i mnil)) = c * nth Z0 ρ i + Z0) (isZ0 c) _ _
    { assume h; rewrite h; simplify; have e : π (c = Z0) { refine isZ0_eq c h }; rewrite e; reflexivity }
    { assume h; rewrite h; reflexivity } }
  { assume c' j r ih;
    refine ind_𝔹_eq (λ b, sumML ρ (if b (if (isZ0 (c + c')) r (mcons (c + c') i r)) (if (nlt i j) (mcons c i (mcons c' j r)) (mcons c' j (minsert c i r)))) = c * nth Z0 ρ i + (c' * nth Z0 ρ j + sumML ρ r)) (Stdlib.Nat.eqn i j) _ _
    { assume heq; rewrite heq; simplify;
      have eij : π (i = j) { refine Stdlib.Nat.eqn_correct i j _; rewrite heq; refine ⊤ᵢ };
      rewrite eij;
      refine ind_𝔹_eq (λ b, sumML ρ (if b r (mcons (c + c') j r)) = c * nth Z0 ρ j + (c' * nth Z0 ρ j + sumML ρ r)) (isZ0 (c + c')) _ _
      { assume hz; rewrite hz; simplify;
        have ez : π (c + c' = Z0) { refine isZ0_eq (c + c') hz };
        rewrite left +_assoc (c * nth Z0 ρ j) (c' * nth Z0 ρ j) (sumML ρ r);
        rewrite left zmul_add_distr_r; rewrite ez; reflexivity }
      { assume hz; rewrite hz; simplify;
        rewrite zmul_add_distr_r; rewrite +_assoc; reflexivity } }
    { assume heq; rewrite heq; simplify;
      refine ind_𝔹_eq (λ b, sumML ρ (if b (mcons c i (mcons c' j r)) (mcons c' j (minsert c i r))) = c * nth Z0 ρ i + (c' * nth Z0 ρ j + sumML ρ r)) (nlt i j) _ _
      { assume hlt; rewrite hlt; simplify; reflexivity }
      { assume hlt; rewrite hlt; simplify; rewrite ih;
        rewrite left +_assoc (c' * nth Z0 ρ j) (c * nth Z0 ρ i) (sumML ρ r);
        rewrite left +_assoc (c * nth Z0 ρ i) (c' * nth Z0 ρ j) (sumML ρ r);
        rewrite (+_com (c' * nth Z0 ρ j) (c * nth Z0 ρ i)); reflexivity } } }
end;

opaque symbol maddML_sound (ρ : 𝕃 int) (l2 : ML) :
  Π l1, π (sumML ρ (maddML l1 l2) = sumML ρ l1 + sumML ρ l2) ≔
begin
  assume ρ l2;
  induction
  { reflexivity }
  { assume c i r ih; simplify; rewrite minsert_sound; rewrite ih; rewrite +_assoc; reflexivity }
end;

opaque symbol mscaleML_sound (ρ : 𝕃 int) (c : ℤ) :
  Π l, π (sumML ρ (mscaleML c l) = c * sumML ρ l) ≔
begin
  assume ρ c;
  induction
  { simplify; symmetry; refine zmul_0_r c }
  { assume c' i r ih;
    refine ind_𝔹_eq (λ b, sumML ρ (if b (mscaleML c r) (mcons (c * c') i (mscaleML c r))) = c * (c' * nth Z0 ρ i + sumML ρ r)) (isZ0 (c * c')) _ _
    { assume hz; rewrite hz; simplify; rewrite ih;
      have ez : π (c * c' = Z0) { refine isZ0_eq (c * c') hz };
      rewrite zmul_add_distr_l; rewrite left (zmul_assoc c c' (nth Z0 ρ i)); rewrite ez; reflexivity }
    { assume hz; rewrite hz; simplify; rewrite ih;
      rewrite zmul_add_distr_l; rewrite (zmul_assoc c c' (nth Z0 ρ i)); reflexivity } }
end;

opaque symbol addNF_sound (ρ : 𝕃 int) (n2 : NF) :
  Π n1, π (denNF ρ (addNF n1 n2) = denNF ρ n1 + denNF ρ n2) ≔
begin
  assume ρ n2 n1;
  refine ind_NF (λ n1, denNF ρ (addNF n1 n2) = denNF ρ n1 + denNF ρ n2) _ n1;
  assume l1 k1;
  refine ind_NF (λ n2, denNF ρ (addNF (mkNF l1 k1) n2) = denNF ρ (mkNF l1 k1) + denNF ρ n2) _ n2;
  assume l2 k2; simplify;
  rewrite maddML_sound; refine zadd4 (sumML ρ l1) (sumML ρ l2) k1 k2
end;

opaque symbol mulNF_sound (ρ : 𝕃 int) (c : ℤ) (n : NF) :
  π (denNF ρ (mulNF c n) = c * denNF ρ n) ≔
begin
  assume ρ c n;
  refine ind_NF (λ n, denNF ρ (mulNF c n) = c * denNF ρ n) _ n;
  assume l k; simplify; rewrite mscaleML_sound; rewrite zmul_add_distr_l; reflexivity
end;

opaque symbol norm_sound (ρ : 𝕃 int) : Π e, π (den ρ e = denNF ρ (norm e)) ≔
begin
  assume ρ;
  induction
  { assume i; simplify; symmetry; refine zmul_1_l (nth Z0 ρ i) }
  { assume z; reflexivity }
  { assume a iha b ihb; simplify; rewrite iha; rewrite ihb;
    symmetry; refine addNF_sound ρ (norm b) (norm a) }
  { assume a iha; simplify; rewrite iha;
    symmetry; rewrite (mulNF_sound ρ (Zneg H) (norm a)); refine zmul_neg1_l (denNF ρ (norm a)) }
  { assume c a iha; simplify; rewrite iha;
    symmetry; refine mulNF_sound ρ c (norm a) }
end;

opaque symbol reflect (ρ : 𝕃 int) (a b : LE) : π (norm a = norm b) → π (den ρ a = den ρ b) ≔
begin
  assume ρ a b h;
  rewrite norm_sound ρ a; rewrite norm_sound ρ b; rewrite h; reflexivity
end;

// ℤ-discreteness bridge: `(1+a ≤ 0) = ¬(-a ≤ 0)` (both ⟺ a < 0, by the integer
// "+1 gap").  PP normalises a `¬(-a≤0)` antecedent to its `1+a≤0` form (AR3's
// `𝟏−a` step); the LP goal keeps the `¬(-a≤0)`, so AR4's `leq (1+a) 0` conclusion
// is transported onto it via `imp_cong_l (disc_eq a)` (see translate/rule_emit AR4).
// Lives here (not Int.lp) for the reflective `(1+a)+(-a)=1` / `1+a=1-(-a)` proofs.
opaque symbol disc_eq (a : τ ι) : π (leq (plus 𝟏 a) 𝟎 = ¬ (leq (neg a) 𝟎)) ≔
begin
  assume a;
  have e1 : π (𝟏 = plus (plus 𝟏 a) (neg a))
    { refine toint_eq 𝟏 (plus (plus 𝟏 a) (neg a)) (from_int_in_int 1) (add_in_int _ _)
        (reflect ((to_int a) ⸬ □) (Llit 1)
           (Ladd (Ladd (Llit 1) (Lvar 0)) (Lneg (Lvar 0))) (eq_refl _)) };
  have e2 : π (plus 𝟏 a = minus 𝟏 (neg a))
    { refine toint_eq (plus 𝟏 a) (minus 𝟏 (neg a)) (add_in_int _ _) (add_in_int _ _)
        (reflect ((to_int a) ⸬ □) (Ladd (Llit 1) (Lvar 0))
           (Ladd (Llit 1) (Lneg (Lneg (Lvar 0)))) (eq_refl _)) };
  refine propExt _ _
    (λ h1 h2, one_not_leq_zero (leq_subst_l e1 (add_leq_zero (plus 𝟏 a) (neg a) h1 h2)))
    (λ h, leq_subst_l e2 (sub_leq 𝟏 (neg a) (discrete (neg a) h)))
end;
