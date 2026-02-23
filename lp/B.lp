require open
  Stdlib.Bool
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

// `prf p` is the type of proofs of `p`
symbol prf : Prd → TYPE;
symbol ▷ ≔ prf; notation ▷ prefix 5;

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

// shorthand: string to expression via variable.
symbol #id ≔ λ str, #var (id str);

// coerce a string to a varaible.
coerce_rule coerce String Var $str ↪ id $str;
/// coerce a string to an expression.
coerce_rule coerce String Exp $str ↪ #var (id $str);
// coerce a varaible to an expression.
coerce_rule coerce Var Exp $x ↪ #var $x;


compute
  ∀ "x" ("x" = "x");

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
