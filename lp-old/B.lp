require open
  Stdlib.Prop Stdlib.Bool
  Stdlib.Classic
  Stdlib.Eq Stdlib.String
  Stdlib.FOL Stdlib.HOL
  Stdlib.List Stdlib.Z;

// datatype for variable-lists.
inductive Var : TYPE ≔
  | id : String → Var
  | ⨾ : Var → Var → Var;
notation ⨾ infix 5;

// datatypes for predicates,
// expressions, and sets:
inductive Prd : TYPE ≔
  | pid : String → Prd
  | TRUE : Prd
  | FALSE : Prd
  | ¬ : Prd → Prd
  | ∧ : Prd → Prd → Prd
  | ∨ : Prd → Prd → Prd
  | ⇒ : Prd → Prd → Prd
  | ⇔ : Prd → Prd → Prd
  | ∀ : Var → Prd → Prd
  | ∃ : Var → Prd → Prd
  | ♢ : Var → Prd → Prd
  | ♡ : Var → Prd → Prd
  | ≃ : Exp → Exp → Prd
  | eql_set : Exp → Exp → Prd
  | ≤ : Exp → Exp → Prd
  | ≪ : Exp → Exp → Prd
  | papp : String → Exp → Prd
  | ∈ : Exp → Exp → Prd
with Exp : TYPE ≔
  | eid : String → Exp
  | eapp : String → Exp → Exp
  | ↦ : Exp → Exp → Exp
  | 𝟎 : Exp
  | 𝟏 : Exp
  | BTRUE : Exp
  | BFALSE : Exp
  | + : Exp → Exp → Exp
  | - : Exp → Exp → Exp
  | ⨪ : Exp → Exp;
type ind_Prd;
// infix notation.
// Precedences from pp-spec §6.1.
// Higher = tighter in lambdapi.
// pp-spec (loose→tight):
//  ⇒(0) ⇔(1) ∧∨(2)
//  ¬(3) =(4) ∈(5)
notation ⇒ infix left 6;
notation ⇔ infix left 7;
notation ∧ infix left 8;
notation ∨ infix left 8;
notation ¬ prefix 9;
notation ≃ infix left 10;
notation ∈ infix left 10;

notation ↦ infix left 10;
notation ≤ infix left 10;
notation ≪ infix left 10;
notation + infix left 12;
notation - infix left 12;
notation ⨪ prefix 13;

// Set codes for inductive types.
symbol prd : Set;
rule τ prd ↪ Prd;
symbol exp : Set;
rule τ exp ↪ Exp;
symbol var : Set;
rule τ var ↪ Var;

// Coerce string to variable.
coerce_rule
  (coerce (String) (Var) $str)
  ↪ id $str;
/// Coerce string to expression.
coerce_rule
  (coerce (String) (Exp) $str)
  ↪ eid $str;
/// Coerce string to predicate.
coerce_rule
  (coerce (String) (Prd) $str)
  ↪ pid $str;
