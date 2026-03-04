require open
  Stdlib.Bool
  Stdlib.Set
  Stdlib.String;

// datatype for variable-lists.
inductive Var : TYPE ≔
  | id : String → Var
  | ⨾ : Var → Var → Var;
notation ⨾ infix right 5;

// datatypes for predicates, expressions, and sets:
inductive Prd : TYPE ≔
  | ¬ : Prd → Prd
  | ∧ : Prd → Prd → Prd
  | ∨ : Prd → Prd → Prd
  | ⇒ : Prd → Prd → Prd
  | ⇔ : Prd → Prd → Prd
  | = : Exp → Exp → Prd
  | ∈ : Exp → Exp → Prd
  | ∀ : Var → Prd → Prd
  | ∃ : Var → Prd → Prd
  | ♢ : Var → Prd → Prd
  | ♡ : Var → Prd → Prd
with Exp : TYPE ≔
  | #var : Var → Exp
  | ↦ : Exp → Exp → Exp
  | × : Exp → Exp → Exp
  | 𝒫 : Exp → Exp
  | big : Exp
  | choice : Exp → Exp
  | comp : Var → Prd → Exp;


type ind_Prd;
// infix notation. precedences given by pp-spec (§6.1).
// higher number = tighter binding in lambdapi.
// pp-spec order (loose→tight): ⇒(0) ⇔(1) ∧∨(2) ¬(3) =(4) ∈(5)
notation ↦ infix 5;
notation × infix 5;
notation ⇒ infix left 6;
notation ⇔ infix left 7;
notation ∧ infix left 8;
notation ∨ infix left 8;
notation ¬ prefix 9;
notation = infix left 10;
notation ∈ infix left 15;

// Set codes for the inductive types.
symbol prd : Set; rule τ prd ↪ Prd;
symbol exp : Set; rule τ exp ↪ Exp;
symbol var : Set; rule τ var ↪ Var;

// shorthand: string to expression via variable.
symbol #id ≔ λ str, #var (id str);

// coerce a string to a varaible.
coerce_rule coerce String Var $str ↪ id $str;
/// coerce a string to an expression.
coerce_rule coerce String Exp $str ↪ #var (id $str);
// coerce a varaible to an expression.
coerce_rule coerce Var Exp $x ↪ #var $x;




// define disequality.
symbol != ≔ λ E F, ¬ (E = F);
notation != infix 20;

// define ⊆ inclusion.
symbol ⊆ ≔ λ s t, s ∈ 𝒫 t;
notation ⊆ infix 10;

// define ⊂ inclusion.
symbol ⊂ ≔ λ s t, (s ⊆ t) ∧ (s != t);
notation ⊂ infix 10;

// syntactic equality, see `Eq.lp`.
sequential symbol var_eq : Var → Var → 𝔹;
sequential symbol exp_eq : Exp → Exp → 𝔹;
sequential symbol prd_eq : Prd → Prd → 𝔹;

// sum type for (Exp + Prd)
inductive Trm : TYPE ≔
  | #exp : Exp → Trm
  | #prd : Prd → Trm;

coerce_rule coerce Prd Trm $P ↪ #prd $P;
coerce_rule coerce Exp Trm $E ↪ #exp $E;

// syntactic equality.
sequential symbol == : Trm → Trm → 𝔹; notation == infix 10;
// define by dispatching on constructor.
rule (#exp $E == #exp $F) ↪ exp_eq $E $F
with (#prd $P == #prd $Q) ↪ prd_eq $P $Q
with (_ == _) ↪ false;

// non-free. see NonFree.lp
symbol nf : Var → Trm → 𝔹;
symbol pnf : Var → Prd → 𝔹;
symbol enf : Var → Exp → 𝔹;

rule nf $x (#prd $P) ↪ pnf $x $P
with nf $x (#exp $E) ↪ enf $x $E;

// substitution. see Subst.lp
symbol sub : Var → Exp → Trm → Trm;
symbol psub : Var → Exp → Prd → Prd;
symbol esub : Var → Exp → Exp → Exp;

rule sub $x $E (#prd $P) ↪ #prd (psub $x $E $P)
with sub $x $E (#exp $F) ↪ #exp (esub $x $E $F);

// boolean-guarded expression.
symbol ?exp : Exp → 𝔹 → Exp;
rule ?exp $E true ↪ $E;

// boolean-guarded predicate.
symbol ?prd : Prd → 𝔹 → Prd;
rule ?prd $P true ↪ $P;

inductive Hyp : TYPE ≔
  | ⦳ : Hyp
  | ∷ : Hyp → Prd → Hyp; notation ∷ infix 1;

symbol dans : Prd → Hyp → 𝔹; notation dans infix 1;
rule ($P dans ⦳)         ↪ false
with ($P dans ($H ∷ $Q)) ↪ prd_eq $P $Q or ($P dans $H);

// containment: N is a conjunct of C (analogous to `dans` for Hyp).
sequential symbol contient : Prd → Prd → 𝔹; notation contient infix 1;

// removal: remove a conjunct from a conjunction.
sequential symbol retirer : Prd → Prd → Prd;

inductive Sqnt : TYPE ≔
  | ⟝ : Hyp → Prd → Sqnt; notation ⟝ infix 1;

symbol ▷ : Sqnt → TYPE;
symbol ⊩ ≔ λ H P, ▷ (H ⟝ P); notation ⊩ infix 1;

// boolean guard: `⁇ b` is inhabited iff `b` computes to `true`.
symbol ⁇ (b : 𝔹) ≔ π (istrue b);

// ---- Results ----
// Some PP rules produce an ancillary result predicate alongside
// their derivation. `Res Σ` is the type of result-derivations for
// sequent Σ.  A value `ρ : Res Σ` encodes a proof of Σ together
// with a result predicate extractable via `obtain ρ`.

injective symbol Res : Sqnt → TYPE;

// `result P` packages a predicate as a result-derivation.
symbol result [Σ] : Prd → Res Σ;

// `obtain ρ` extracts the result predicate.
symbol obtain [Σ] : Res Σ → Prd;

// `obtain` is the inverse of `result`.
rule obtain (result $P) ↪ $P;

// notational shorthand: Σ ⇝ R  means  "the proof of Σ gives result R".
symbol ⇝ (Σ : Sqnt) (R : Prd) ≔ Res Σ; notation ⇝ infix 1;

// --- predicates not yet in the inductive type ---
// TRUE and FALSE as predicates.
symbol TRUE : Prd;
symbol FALSE : Prd;

// arithmetic inequality (normalised form: E ≤ 0).
symbol ≤ : Exp → Exp → Prd; notation ≤ infix left 10;
// strict inequality marker (used to avoid looping in AR5–AR8).
symbol ≪ : Exp → Exp → Prd; notation ≪ infix left 10;

// set equality predicate (introduced by Set Translator).
symbol eql_set : Exp → Exp → Prd;

// arithmetic expression constructors.
symbol 𝟎 : Exp;
symbol 𝟏 : Exp;
symbol + : Exp → Exp → Exp; notation + infix left 12;
symbol - : Exp → Exp → Exp; notation - infix left 12;
symbol ⨪ : Exp → Exp; notation ⨪ prefix 13;  // unary minus

// B-method boolean values (expressions, not predicates).
symbol BTRUE : Exp;
symbol BFALSE : Exp;
