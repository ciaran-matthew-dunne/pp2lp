# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

Scope: this is the **paper** for the `pp2lp` project — a tool paper for
**LPAR-26** (Experimental & Tool track). For the *tool itself* (the OCaml
emitter, the `lp/rules/` encoding, the benchmark suites), see the repo-root
`../../CLAUDE.md`; do not duplicate or overwrite it.

## Build

```
make            # latexmk -lualatex + biber  ->  pp2lp.pdf
make watch      # latexmk -pvc (continuous preview)
make clean      # latexmk -C + remove .bbl/.bcf/.run.xml
```

**Must compile with lualatex** (not pdflatex): the source uses
`unicode-math` + `newcomputermodern`, and the LambdaPi/replay code listings
contain raw Unicode (π ⋀ ♢ ♡ ∷ 𝕃 ≔ …). Bibliography is **biblatex + biber**.
Toolchain needed: TeXLive (with `newcomputermodern`), `biber`, and the
JetBrains Mono font.

## Structure

`pp2lp.tex` is the entry point: `\documentclass[EPiC]{easychair}`, then it
`\input`s, in order, `preamble.tex`, `macros.tex`, `results-data.tex`, and
the six section files `intro / background / encoding / replay / eval /
conclusion`. Each section is one file with one `\section`.

Section status (what to expand vs. polish):
- **Full drafts:** `intro.tex` (trust-gap lead + pipeline figure),
  `encoding.tex` (the core — `AND2` figure, soundness-proved framing).
- **Skeletons to flesh out:** `background.tex`, `replay.tex` (has the
  reconstruction figure), `eval.tex` (has the results table), `conclusion.tex`.

## Conventions that bite if you don't know them

- **All benchmark numbers live in `results-data.tex`** and nowhere else.
  `eval.tex`'s table and prose only reference the macros (`\ogPass`,
  `\prvTot`, `\numRulesCovered`, …). Tool and paper move together, so these
  change often: edit `results-data.tex` and refresh its dated comment block;
  never hard-code a number in prose.
- **Listing glyphs are mapped, not magic.** Code blocks are written with raw
  Unicode and rendered via the `literate=` table in `preamble.tex`'s
  `\lstdefinestyle{lp}`. A glyph with no entry there renders as tofu (or
  errors). To show a new symbol in code, add a `{glyph}{{$...$}}1` rule.
  `mathescape=true` is on, so `$...$` also works inside listings.
- **Side-by-side code figures use `minipage`, never TikZ `\node{...}`.**
  `lstlisting`/`tcblisting` break when grabbed as a TikZ node argument. See
  the `AND2` figure (`encoding.tex`) and the reconstruction figure
  (`replay.tex`) for the pattern. The full-width pipeline figure uses the
  `boxfigure` env (`jbw-boxfigure.sty`).
- **Code-box environments are `codeLP` / `codePP`** (tcblisting wrappers in
  `preamble.tex`). Do not name one `lpcode` — that clashes with a predefined
  macro and the build dies with "Command \lpcode already defined".
- **The class loads `hyperref` itself.** Use `\hypersetup{...}` in the
  preamble; do not `\usepackage{hyperref}`. `easychair.cls` is vendored here
  (copied from `~/Isabelle2025/contrib/easychair-3.5/`); `notimes` is its
  default, which is why `unicode-math` drops in.
- **Page budget:** ≤ 8 pages **excluding** the bibliography (LPAR tool
  track). Body currently ≈ 6.5pp, so there is room to grow the skeletons.

## Framing (agreed with the author — keep consistent)

- Lead = the **trust gap**: independently checking Atelier B's closed-source
  Predicate Prover. Working title in `pp2lp.tex`.
- The differentiator vs. eo2lp / Coltellacci-style reconstruction: each PP
  rule is **proved sound** (an `opaque symbol` with a real proof body over
  the small `B.lp` kernel), *not* axiomatized. Preserve this emphasis.
- Evaluation: lead with the non-arithmetic 100% (`og`, `prv-no-arith`);
  present full `prv` transparently; the arithmetic-normalisation rules
  (NRM27–30, which dispatch to PP's closed solver) are the principled gap.

## Open items

`grep -rn TODO *.tex *.bib` lists everything needing author confirmation:
co-author affiliations/emails, the `pp2lp` GitHub URL, the PP-specification
citation (`pp_spec`) and other `VERIFY`-marked bib entries, exact rule
counts, and refreshing the reconstruction figure from a live `og` trace.

## Style reference

The author's eo2lp paper at `~/prog/eo2lp/tex` is the model for voice,
macros, and figure style (it targets LNCS; this paper uses EasyChair/EPiC).
