require open pp2lp.B pp2lp.ConjList pp2lp.Quant pp2lp.rules.Res;

symbol mem : Prop → 𝕃* o → Prop;
rule mem _  ∎          ↪ ⊥
with mem $P ($ps ∷ $Q) ↪ (mem $P $ps) ∨ ($P = $Q);

opaque symbol mem_sound (P : Prop)
  : Π ps : 𝕃* o, π (mem P ps) → π (⋀ ps) → π P ≔
begin
  assume P;
  induction
  { assume hmem hconj; refine ⊥ₑ hmem }
  { assume ps ih Q hmem hconj;
    refine ∨ₑ hmem _ _
    { assume hin; refine ih hin (⋀_init hconj) }
    { assume heq; refine =⇒ (eq_sym heq) (⋀_last hconj) } }
end;

// ============ ⇒R rules: peel a binder by instantiation (trust-free) ============

// NRM30: unary ♡x, general witness b.  Instantiate at b, feed premise.
opaque symbol NRM30' [ps : τ ι → 𝕃* o] [R : Prop] (b : τ ι)
  : π (¬ ⋀ (ps b) ⇒ R)
  → π ((`♡ v : Tuple 1, ¬ ⋀ (ps (prj 0 v))) ⇒ R) ≔
begin
  assume ps R b h_prem h♡;
  refine h_prem (♡_to_pi (λ v : Tuple 1, ¬ ⋀ (ps (prj 0 v))) h♡ (unit ⨾ b))
end;

// NRM28: x := 𝟎 specialisation of NRM30.
opaque symbol NRM28' [ps : τ ι → 𝕃* o] [R : Prop]
  : π (¬ ⋀ (ps 𝟎) ⇒ R)
  → π ((`♡ v : Tuple 1, ¬ ⋀ (ps (prj 0 v))) ⇒ R) ≔
begin
  assume ps R h_prem h♡;
  refine h_prem (♡_to_pi (λ v : Tuple 1, ¬ ⋀ (ps (prj 0 v))) h♡ (unit ⨾ 𝟎))
end;

// NRM29: multi-binder, pin the prj0 slot to b v' (witness a function of the
// remaining binders — e.g. b v' = — prj 0 v' for the sum-zero case).
opaque symbol NRM29' [n] [ps : Tuple (+1 n) → 𝕃* o] [R : Prop] (b : Tuple n → τ ι)
  : π ((`♢ v' : Tuple n, ¬ ⋀ (ps (v' ⨾ b v'))) ⇒ R)
  → π ((`♡ v : Tuple (+1 n), ¬ ⋀ (ps v)) ⇒ R) ≔
begin
  assume n ps R b h_prem h♡;
  refine h_prem (pi_to_♢ (λ v', ¬ ⋀ (ps (v' ⨾ b v')))
    (λ v', ♡_to_pi (λ v, ¬ ⋀ (ps v)) h♡ (v' ⨾ b v')))
end;
