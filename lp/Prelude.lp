// Prelude.lp — the whole library surface in one open.
//
// Re-exports the trusted base (B), the proved lemmas (lemmas/*), and every
// per-section rule module (rules/*). Emitted goal files open just this:
// `require open pp2lp.Prelude;`.
require open
  pp2lp.B
  pp2lp.lemmas.Int pp2lp.lemmas.Zmul pp2lp.lemmas.Reflect pp2lp.lemmas.Tuple pp2lp.lemmas.ConjList
  pp2lp.rules.Res
  pp2lp.rules.Conj pp2lp.rules.Disj
  pp2lp.rules.Impl pp2lp.rules.Equiv
  pp2lp.rules.Neg pp2lp.rules.Axm
  pp2lp.rules.TrueFalse
  pp2lp.rules.All pp2lp.rules.Xst
  pp2lp.rules.Nrm pp2lp.rules.Eq
  pp2lp.rules.Arith pp2lp.rules.Bool;
