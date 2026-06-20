# CLAUDE.md — the paper (`tex/`)

Writing guidance for the LPAR-26 paper. The repo-root `CLAUDE.md` carries the
project and tool context; this file governs prose under `tex/`. The paper sources
live in `tex/paper/`.

**Stakes.** LPAR-26, Experimental & Tool track: **8 pages excluding bibliography
and appendices**, single-blind, artifact link required, deadline **21 Jun 2026
AoE**. The CFP says papers "indistinguishable from AI slop will be desk
rejected," and the reviewers are logic / automated-reasoning / proof-assistant
experts. So every sentence must read as if a careful human wrote it, and you may
assume the reader knows logical frameworks, dependent types, rewriting, and
SMT/hammer proof reconstruction — motivate the *specific* contribution, never the
background.

**Match the draft's voice — consistency beats local cleverness.** The current
prose is dense, concrete, and declarative, with little hedging. Read a passage's
neighbours before editing it and write in the same register; don't rewrite
untouched text to suit your taste.

**The math-writing canon (Halmos, Knuth), distilled:**
- *Say something, to someone.* One idea per paragraph; cut sentences that merely
  restate it. State the idea informally, then formalise, then give the concrete
  instance — the draft already does this (e.g. the `AND4_1`/`ALL7` result example).
- *Be ruthlessly consistent in terminology and notation* — the SAME word and
  symbol for the SAME concept, every time (result, replay, sequent, rule lemma;
  the `\rn{}` names; `\Prf`/`\El`). This OVERRIDES the generic "vary your wording
  to dodge AI detectors" advice: vary connective prose, never a technical term.

**AI-tell vocabulary — do not use:** delve, showcase, leverage (vb), boast,
harness (vb), underscore, foster, robust, seamless, comprehensive, holistic,
nuanced, multifaceted, intricate, crucial, pivotal, vital, paradigm, realm,
landscape, tapestry, testament, elevate, unlock, empower, streamline,
cutting-edge; and empty self-praise ("powerful", "elegant", "novel"). Keep the
internal coinages out of the paper too: 'frontier', 'gate', 'provenance', 'fails
loud' (and say 'result-consuming', not 'branching quantifier').

**AI-tell rhythm — do not write:**
- "It's not just X, it's Y", or an inflated "not only … but also".
- The rule of three as a default beat (three parallel adjectives / clauses).
- Stacked transition openers (Moreover, Furthermore, Additionally, Notably) —
  rare at most, never two in a row.
- Signposting filler ("In this section we…", "It is worth noting that…").
- A section-closing sentence that recaps the section.
- Hedge pile-ups ("generally / typically / arguably") or vague intensifiers
  ("very / significantly") standing in for a number.
- Em-dashes are fine: the draft uses `---` sparingly — keep that level, don't
  make them the default connector, and don't "fix" the existing ones.

**Truthfulness (an LLM's two failure modes here):**
- *Never invent a citation or bibkey.* `paper/pp2lp.bib` is the source of truth;
  cite only keys that exist there. If a reference is needed but missing, leave
  `% TODO(authors): cite …` — a fabricated reference is an instant credibility
  loss with these reviewers.
- *Claims must match the artifact and the numbers.* Every benchmark figure is a
  macro in `paper/results-data.tex` (`\allPass`, `\prvReplayed`, …) — never
  hard-code a number in prose, and never state a result the tool/proofs don't
  support. The abstract's "nearly all rules" / "every replay reconstructed" must
  stay literally true; if the work changes, change the claim.

**Repo/LaTeX conventions** (part of not looking machine-made; files under `paper/`):
- Use the macros for every system / format / rule name: `\pp`, `\lp`, `\tool`,
  `\ab`, `\dedukti`, `\bmethod`, `\lpcmr`, `\trace`, `\replay`, `\butf`, `\lpf`,
  `\rn{…}`, and the logic macros (`\Prf`, `\El`, `\Prop`, `\Res`, …). Grep
  `macros.tex` first; never spell a name out raw.
- One sentence per source line, sentences separated by a lone `%` (keeps diffs
  sentence-granular and suppresses stray spaces). Cross-refs via `\autoref`.
- LP/replay code goes in `codeLP`/`codePP`/`codeLPmulti` boxes; any new non-ASCII
  glyph needs a `literate` entry in `preamble.tex` or it renders as tofu (big
  operators like ⋀ via `$\bigwedge$`).
- `conclusion.tex` is a stale skeleton — the live conclusion is the last section
  of `eval.tex`. Build is lualatex + biber.

**Voice-mode collaboration.** Criticisms arrive by imperfect speech-to-text. If
an instruction — especially a symbol, rule name, or bibkey — looks
mis-transcribed, confirm before acting. Make the smallest edit that addresses the
criticism, say what changed, and prefer tightening over adding (the page budget
is hard). Read the edited sentence back: does it scan, and is it backed by the
artifact?
