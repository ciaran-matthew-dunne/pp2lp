# Handoff Notes

## Session Summary

This session fixed all 6 XFAIL PRV tests (86/86 now pass), proved 12 admitted LP rules, fixed 2 broken rule types, and improved INS contradiction resolution in the emitter.

## Changes Made

### 1. Fix AR5/AR6/AR7/AR8 rule signatures (`lp/rules/Arith.lp`)

The LP encodings of AR5-AR8 had wrong argument structure vs the PP spec:
- **AR5/AR6**: First arg changed `≪` → `≤` (side condition from H). Child arg reordered to match PP antecedent: `(—a ≪ 0) ⇒ ((a = 0) ⇒ R)` instead of swapped `(a = 0) ⇒ ((—a ≤ 0) ⇒ R)`.
- **AR7/AR8**: Same `≪` → `≤` fix for side conditions. Equality direction changed `a = b` → `b = a`. Child arg uses `≪` (matching spec) instead of `≤`.
- **AR7**: `c` made explicit parameter (not determinable from result type, only in trusted args).
- **AR8**: `a` made explicit parameter (appears in child equality, extracted by emitter).

These fixes unblocked AR12 after AR5/AR8, fixing equality_004, equality_013, equality_014, negation_003 (4 tests).

### 2. AR12 hypothesis introduction (`ocaml/src/emit_lp.ml`)

Added AR12 to the `introduce` function: after `refine AR12 _`, emit `assume hN` to introduce the `≤` hypothesis (AR12 converts `(a ≪ b) ⇒ P` to `(a ≤ b) → P`).

### 3. AR7/AR8 explicit parameter emission (`ocaml/src/emit_lp.ml`)

`emit_ar78_args` now extracts the explicit parameter from the child node:
- AR8: extracts `a` from the child's leading equality RHS
- AR7: provides `𝟎` as dummy `c` (unused in child type)

### 4. Proved 12 LP rules

**Arith.lp** (2 rules):
- **AR2**: `¬(a ≤ b) → (a ≤ b) ⇒ R` — ex falso
- **AR9**: `E = F → (F ≤ 0) ⇒ R → (E ≤ 0) ⇒ R` — rewrite via `have`

**Nrm.lp** (8 rules — file is now fully proved, 0 admits):
- **NRM8**: identity (♢ = ♡ = ∀)
- **NRM8_13**: classical contraposition (same pattern as NRM8_13_3)
- **NRM19, NRM19_2**: witness contradiction via `⊥ₑ (hf E (∧ᵢ ⊤ᵢ hr))`
- **NRM20, NRM21, NRM22, NRM23**: equality elimination under ♡ via `eq_refl`/`eq_sym`

**Eq.lp** (1 rule — file is now fully proved, 0 admits):
- **EQS2**: contrapositive of `set_ext` forward direction

### 5. Fixed EQS2_1 type (`lp/rules/Eq.lp`)

EQS2_1 had wrong input type `(⊥ ⇒ R) = S` (following incorrect PP spec). Fixed to `(¬(E = F) ⇒ R) = S` mirroring the base EQS2 rule. Now fully proved using `propExt` + `set_ext`.

### 6. INS contradiction resolution (`ocaml/src/emit_lp.ml`)

Added `heart_resolve` strategy: when the simple `¬P`/`P` pair lookup fails, scan context for a `♡`-hypothesis `∀ xs, ¬(C₁ ∧ ... ∧ Cₙ)` and build `h_heart _ ... (∧ᵢ (∧ᵢ c₁ c₂) ... cₙ)` from the conjunct hypotheses.

Safety checks:
- Conjunction arity must match number of conjunct hypotheses
- Skeleton comparison (ignoring `$`-bound variable names) rejects wrong ♡-hyp (e.g., different set)
- Rejects Leq leaves (may be AR3_F-normalized in AST but not in LP proof state)
- Tries multiple ♡-hyps, skipping non-matching ones

Result: 88 → 62 INS admits (26 fixed). Remaining 62 involve AR3_F arithmetic normalization mismatch.

## Known Issues

### AR3_F normalization mismatch
When AR3_F (a HOAS-identity rule) normalizes a `♡`-hyp body (converting `¬(E ≤ 0)` to `(1-E ≤ 0)`), the emitter's AST sees the post-normalization form but LP retains the original. This causes heart_resolve to emit structurally incorrect proof terms. The `no_arith` Leq-leaf check prevents this, but it also blocks valid resolutions where Leq leaves happen to match.

### Remaining admits in Arith.lp
8 rules remain admitted. AR5/AR6 can't be proved from their types alone (child type has `≪` where `≤` is needed). AR3/AR4/AR9_1 have solver facts encoded as `π ⊤`. AR7/AR8 combine both issues. AR13 needs integer arithmetic axioms.

## Test Status
- **Traces:** 30/30 pass
- **PRV benchmarks:** 86/86 pass (0 xfail)
- **OCaml unit tests:** 118 pass
- **Generated proof admits:** 192 (down from 218)
