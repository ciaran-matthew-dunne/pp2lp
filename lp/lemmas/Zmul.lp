// lemmas/Zmul.lp — ℤ ring multiplication laws (commutativity, associativity,
// distributivity), proved from the binary Stdlib.Pos/Stdlib.Z representation.
// Stdlib provides the additive laws (+_assoc/+_com) and the operations but NO
// multiplicative lemmas, so the reflective coefficient normalizer (Reflect.lp)
// builds them here.  Pos lemmas first, then lifted to ℤ.
require open Stdlib.Pos;

// ---- Pos multiplication laws (mul recurses structurally on its 1st arg) ----
// mul by H on the right
opaque symbol mul_H_r : Π q, π (mul q H = q) ≔
begin
  induction
  { assume x ih; simplify; rewrite ih; reflexivity }   // I x
  { assume x ih; simplify; rewrite ih; reflexivity }   // O x
  { reflexivity }                                       // H
end;

// mul by O on the right
opaque symbol mul_O_r : Π q p, π (mul q (O p) = O (mul q p)) ≔
begin
  induction
  { assume x ih p; simplify; rewrite ih; reflexivity }  // I x: add (O p) (O (O (mul x p)))
  { assume x ih p; simplify; rewrite ih; reflexivity }  // O x
  { assume p; reflexivity }                             // H
end;

opaque symbol add_swap a b c : π (add a (add b c) = add b (add a c)) ≔
begin assume a b c; rewrite left add_assoc a b c; rewrite (add_com a b);
  rewrite add_assoc; reflexivity end;

// mul by I on the right
opaque symbol mul_I_r : Π q p, π (mul q (I p) = add q (O (mul q p))) ≔
begin
  induction
  { assume x ih p; simplify; rewrite ih; refine feq I (add_swap p x (O (mul x p))) }  // I x
  { assume x ih p; simplify; rewrite ih; reflexivity }  // O x
  { assume p; reflexivity }                             // H
end;

opaque symbol mul_com : Π p q, π (mul p q = mul q p) ≔
begin
  induction
  { assume x ih q; simplify; rewrite mul_I_r; rewrite ih; reflexivity }  // I x
  { assume x ih q; simplify; rewrite mul_O_r; rewrite ih; reflexivity }  // O x
  { assume q; symmetry; refine mul_H_r q }                               // H
end;

opaque symbol padd4 a b c d : π (add (add a b) (add c d) = add (add a c) (add b d)) ≔
begin assume a b c d;
  rewrite add_assoc; rewrite left add_assoc b c d; rewrite (add_com b c);
  rewrite add_assoc c b d; rewrite left add_assoc a c (add b d); reflexivity end;

opaque symbol mul_add_distr_l : Π p q r, π (mul p (add q r) = add (mul p q) (mul p r)) ≔
begin
  induction
  { assume x ih q r; simplify; rewrite ih; refine padd4 q r (O (mul x q)) (O (mul x r)) }  // I x
  { assume x ih q r; simplify; rewrite ih; reflexivity }   // O x
  { assume q r; reflexivity }                              // H
end;

opaque symbol mul_add_distr_r : Π p q r, π (mul (add p q) r = add (mul p r) (mul q r)) ≔
begin assume p q r;
  rewrite mul_com (add p q) r; rewrite mul_add_distr_l;
  rewrite (mul_com r p); rewrite (mul_com r q); reflexivity end;

opaque symbol pmul_assoc : Π p q r, π (mul (mul p q) r = mul p (mul q r)) ≔
begin
  induction
  { assume x ih q r; simplify; rewrite mul_add_distr_r; simplify; rewrite ih; reflexivity }  // I x
  { assume x ih q r; simplify; rewrite ih; reflexivity }   // O x
  { assume q r; reflexivity }                              // H
end;

// ======== lift to ℤ ========
require open Stdlib.Z;

opaque symbol zmul_com : Π x y, π (x * y = y * x) ≔
begin
  induction
  { assume y; simplify; reflexivity }                       // Z0
  { assume px; induction
    { reflexivity }
    { assume py; refine feq Zpos (mul_com px py) }
    { assume py; refine feq Zneg (mul_com px py) } }
  { assume px; induction
    { reflexivity }
    { assume py; refine feq Zneg (mul_com px py) }
    { assume py; refine feq Zpos (mul_com px py) } }
end;

opaque symbol zmul_assoc : Π x y z, π ((x * y) * z = x * (y * z)) ≔
begin
  induction
  { assume y z; simplify; reflexivity }
  { assume px; induction
    { assume z; simplify; reflexivity }
    { assume py; induction
      { reflexivity }
      { assume pz; refine feq Zpos (pmul_assoc px py pz) }
      { assume pz; refine feq Zneg (pmul_assoc px py pz) } }
    { assume py; induction
      { reflexivity }
      { assume pz; refine feq Zneg (pmul_assoc px py pz) }
      { assume pz; refine feq Zpos (pmul_assoc px py pz) } } }
  { assume px; induction
    { assume z; simplify; reflexivity }
    { assume py; induction
      { reflexivity }
      { assume pz; refine feq Zneg (pmul_assoc px py pz) }
      { assume pz; refine feq Zpos (pmul_assoc px py pz) } }
    { assume py; induction
      { reflexivity }
      { assume pz; refine feq Zpos (pmul_assoc px py pz) }
      { assume pz; refine feq Zneg (pmul_assoc px py pz) } } }
end;

// ---- helpers: z * (Zpos of a Pos constructor) ----
opaque symbol zmul_1_r : Π z, π (z * Zpos H = z) ≔
begin induction
  { reflexivity }
  { assume p; refine feq Zpos (mul_H_r p) }
  { assume p; refine feq Zneg (mul_H_r p) } end;

opaque symbol zmul_O_r : Π z c, π (z * Zpos (O c) = double (z * Zpos c)) ≔
begin induction
  { assume c; reflexivity }
  { assume p c; simplify; rewrite mul_O_r; reflexivity }
  { assume p c; simplify; rewrite mul_O_r; reflexivity } end;

opaque symbol zmul_I_r : Π z c, π (z * Zpos (I c) = double (z * Zpos c) + z) ≔
begin induction
  { assume c; reflexivity }
  { assume p c; simplify; rewrite mul_I_r; refine feq Zpos (add_com p (O (mul p c))) }
  { assume p c; simplify; rewrite mul_I_r; refine feq Zneg (add_com p (O (mul p c))) } end;

// ℤ 4-term AC rearrangement
opaque symbol z_add4 a b c d : π ((a + b) + (c + d) = (a + c) + (b + d)) ≔
begin assume a b c d;
  rewrite +_assoc; rewrite left +_assoc b c d; rewrite (+_com b c);
  rewrite +_assoc c b d; rewrite left +_assoc a c (b + d); reflexivity end;

// ---- refl bridges (LHS reduces from RHS, so eq_refl proves them) ----
opaque symbol sub_to_add a b : π (sub a b = Zpos a + Zneg b) ≔ begin reflexivity end;
opaque symbol double_sub a b : π (double (sub a b) = sub (O a) (O b)) ≔ begin reflexivity end;
opaque symbol zpos_add a b : π (Zpos (add a b) = Zpos a + Zpos b) ≔ begin reflexivity end;
opaque symbol zneg_add a b : π (Zneg (add a b) = Zneg a + Zneg b) ≔ begin reflexivity end;

// double(sub a b) + sub p q = sub (add p (O a)) (add q (O b))   [the I-case core]
opaque symbol sub_double_add a b p q :
  π (double (sub a b) + sub p q = sub (add p (O a)) (add q (O b))) ≔
begin assume a b p q;
  rewrite double_sub; rewrite sub_to_add (O a) (O b); rewrite sub_to_add p q;
  rewrite sub_to_add (add p (O a)) (add q (O b));
  rewrite zpos_add p (O a); rewrite zneg_add q (O b);
  rewrite z_add4 (Zpos (O a)) (Zneg (O b)) (Zpos p) (Zneg q);
  rewrite (+_com (Zpos (O a)) (Zpos p)); rewrite (+_com (Zneg (O b)) (Zneg q));
  reflexivity
end;

opaque symbol sub_mul_Zpos : Π p q c, π ((sub p q) * Zpos c = sub (mul p c) (mul q c)) ≔
begin
  assume p q;
  induction
  { assume c ih; rewrite zmul_I_r; rewrite ih; rewrite mul_I_r; rewrite mul_I_r;
    refine sub_double_add (mul p c) (mul q c) p q }     // I c
  { assume c ih; rewrite zmul_O_r; rewrite ih; rewrite mul_O_r; rewrite mul_O_r; reflexivity }  // O c
  { rewrite zmul_1_r; rewrite mul_H_r; rewrite mul_H_r; reflexivity }   // H
end;

// x * Zneg c = — (x * Zpos c)   (by cases on x)
opaque symbol mul_Zneg : Π x c, π (x * Zneg c = — (x * Zpos c)) ≔
begin induction
  { assume c; reflexivity }
  { assume p c; reflexivity }
  { assume p c; reflexivity } end;

// distributivity for a POSITIVE multiplier
opaque symbol zmul_add_distr_pos : Π x y c, π ((x + y) * Zpos c = x * Zpos c + y * Zpos c) ≔
begin
  induction
  { assume y c; simplify; reflexivity }              // x = Z0
  { assume px; induction
    { assume c; simplify; reflexivity }              // Zpos, Z0
    { assume py c; refine feq Zpos (mul_add_distr_r px py c) }   // Zpos, Zpos
    { assume py c; refine sub_mul_Zpos px py c } }              // Zpos, Zneg
  { assume px; induction
    { assume c; simplify; reflexivity }              // Zneg, Z0
    { assume py c; refine sub_mul_Zpos py px c }                // Zneg, Zpos
    { assume py c; refine feq Zneg (mul_add_distr_r px py c) } } // Zneg, Zneg
end;

// distributivity for ANY multiplier
opaque symbol zmul_add_distr_r : Π x y z, π ((x + y) * z = x * z + y * z) ≔
begin
  assume x y;
  induction
  { simplify; reflexivity }                          // z = Z0
  { assume c; refine zmul_add_distr_pos x y c }      // z = Zpos c
  { assume c; rewrite (mul_Zneg (x + y) c); rewrite (mul_Zneg x c); rewrite (mul_Zneg y c);
    rewrite zmul_add_distr_pos; rewrite distr_—_+; reflexivity }   // z = Zneg c
end;

// ---- derived: left distributivity, identities, scaling ----
opaque symbol zmul_add_distr_l a x y : π (a * (x + y) = a * x + a * y) ≔
begin assume a x y;
  rewrite (zmul_com a (x + y)); rewrite zmul_add_distr_r;
  rewrite (zmul_com x a); rewrite (zmul_com y a); reflexivity end;

opaque symbol zmul_0_r c : π (c * Z0 = Z0) ≔ begin reflexivity end;

opaque symbol zmul_1_l x : π (Zpos H * x = x) ≔
begin assume x; rewrite (zmul_com (Zpos H) x); refine zmul_1_r x end;

opaque symbol zmul_neg1_l : Π x, π (Zneg H * x = — x) ≔
begin induction { reflexivity } { assume p; reflexivity } { assume p; reflexivity } end;
