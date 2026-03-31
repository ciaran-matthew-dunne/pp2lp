# Lambdapi Reference (v3.0.0)

Lambdapi is a logical framework with dependent types and rewriting.
No pre-defined logic: users define their own with symbols and rules.
Compatible with Dedukti (`.dk` files); can export to Coq.

---

## 1. Terms

### 1.1 Identifiers

- **Regular:** non-empty UTF-8 sequence excluding `` \t\r\n :,;`(){}[]".@$|?/ ``, and not an integer. `/` alone is valid.
- **Escaped:** any sequence between `{|` and `|}`. `{|i|}` = `i`.
- **Convention:** uppercase = types (`Nat`); lowercase = constructors/functions/proofs (`zero`).

### 1.2 Qualified Identifiers

`dir1.`...`dirn.file.id` denotes symbol `id` in `dir1/.../dirn/file.lp`.
Must be `require`'d first. Path components cannot be natural numbers.

### 1.3 Term Syntax

| Form | Meaning |
|------|---------|
| `TYPE` | sort for types |
| `x` | bound variable |
| `f`, `M.f` | (qualified) symbol |
| `@f` | disable implicit args |
| `lambda (x:A) y z, t` | function |
| `Π (x:A) y z, T` | dependent product |
| `A -> T` | non-dependent product (sugar for `Π _:A, T`) |
| `let f (x:A) y z : T := t in u` | let-binding |
| `f x y` | application (juxtaposition) |
| `x + y` | infix (if notation declared) |
| `(+)` or `@+` | notationless value of infix symbol |
| `?0.[x;y]` | metavariable application (`?0` alone = `?0.[]`) |
| `$P.[x;y]` | pattern variable (rules only) |
| `_` | wildcard (fresh metavar in terms; fresh pattern var in LHS) |
| `[t]` | explicit implicit argument |
| `"hello"` | string literal (needs `builtin "String"`) |
| `42` | numeric literal (needs numeric builtins) |

### 1.4 Builtins for Literals

```
builtin "String" := ...; // : TYPE

// Decimal integers:
builtin "0" := ...; ... builtin "10" := ...; // : T
builtin "+" := ...; // : T -> T -> T
builtin "*" := ...; // : T -> T -> T
builtin "-" := ...; // : T -> T   (optional, for negatives)
```

### 1.5 Decimal Printing Builtins

```
builtin "nat_zero" := ...; builtin "nat_succ" := ...;             // Peano: N, N->N
builtin "pos_one" := ...;  builtin "pos_double" := ...;           // Positive base-2: P, P->P
                           builtin "pos_succ_double" := ...;      //   P->P
builtin "int_zero" := ...; builtin "int_positive" := ...;         // Integers: Z, P->Z
                           builtin "int_negative" := ...;         //   P->Z
```

---

## 2. Commands

Commands end with `;`. Comments: `//` (line), `/* ... */` (block, nestable).

### 2.1 `require`

Import symbols/rules/builtins. Dependencies are transitively inherited.
Always takes qualified identifiers. Aliased modules cannot be opened.

```
require std.bool;
require church.list as list;
```

### 2.2 `open`

Put symbols of required modules into scope. Non-`private` opens are
transitively inherited. Always takes qualified identifiers.

```
require open std.bool;       // combined
open std.bool;               // separate
private open std.bool;       // non-transitive
```

### 2.3 `symbol`

```
<modifiers> symbol <id> <params> [: <type>] [:= <term>] [begin <proof> end];
```

Without `:=`: declaration/axiom (proof script only helps solve
unification constraints, does NOT prove the type).
With `:=`: definition. `symbol f:A := t` = `symbol f:A := begin refine t end`.

```
symbol N : TYPE;                          // declaration
symbol add : N -> N -> N;                 // declaration
symbol double n := add n n;               // definition (type inferred)
symbol triple n : N := add n (double n);  // definition with annotation
```

#### Modifiers

| Modifier | Effect |
|----------|--------|
| `opaque` | never reduced to definition |
| `constant` | no rule or definition allowed |
| `injective` | `f t1..tn = f u1..un` implies `ti = ui` (user-verified) |
| `commutative` | `f t u = f u t` in conversion |
| `[left\|right] associative` | `f (f t u) v = f t (f u v)` (requires `commutative`) |
| `private` | cannot be used outside its module |
| `protected` | only in LHS of rules outside its module |
| `sequential` | rules applied in declaration order |

**AC canonical forms:** Commutative: `f t u` has `t <= u`.
Commutative + associative left: flat left-associated, args sorted.
Commutative + associative [right]: flat right-associated, args sorted.

**Exposition rules:** Private symbols cannot appear in public symbol
types or public rule RHS. External protected symbols cannot head a LHS
or appear in any RHS.

#### Implicit Arguments

Enclose in `[...]`. At use-sites replaced by `_`. Override with `[t]` or `@f`.

```
symbol eq [a:U] : T a -> T a -> Prop;
// eq t u, eq [_] t u, @eq _ t u
```

### 2.4 `rule`

Pattern variables prefixed by `$`. Multiple rules joined with `with`.

```
rule add zero      $n |-> $n
with add (succ $n) $m |-> succ (add $n $m);
```

Assumed confluent and terminating. Lambdapi auto-checks local
confluence (critical pairs, except AC/non-nullary pattern vars)
and subject reduction. Use `--confluence`/`--termination` for external tools.

**Higher-order patterns** (a la Miller, modulo beta):
`$F.[x;y]` = distinct bound vars that may occur in match.
`$P.[]` = no bound vars allowed. `$P` = shorthand for `$P.[]`
when not under binder. Unnamed: `$_.[x;y]`. Wildcard `_` =
most general (all in-scope vars).

Pattern vars cannot head applications (`$F.[] x` illegal, `x $F.[]` ok).
LHS lambdas cannot have type annotations.

**Unlike OCaml/Coq/Agda:** LHS can contain defined symbols, overlap, be non-linear:

```
rule add (add x y) z |-> add x (add y z);  // defined in LHS
rule minus x x |-> zero;                    // non-linear
```

### 2.5 `notation`

| Kind | Example | Notes |
|------|---------|-------|
| `infix left N` | `notation + infix left 6.5;` | type `A -> A -> A` |
| `infix right N` | `notation :: infix right 5;` | type `A -> A -> A` |
| `prefix N` | `notation not prefix 5;` | |
| `postfix N` | `notation ! postfix 10;` | |
| `quantifier` | `notation forall quantifier;` | `` `f x, t `` = `f (lambda x, t)` |

Priorities are floats. All operator kinds share priority levels.
`f x` (application) > any operator > `->` (arrow).
Hence `- f x` = `- (f x)` and `- A -> A` = `(- A) -> A`.
Use `(+)` or `@+` for notationless value. Can assign to symbols from other modules.

### 2.6 `builtin`

Map internal string to user symbol: `builtin "String" := MyString;`

### 2.7 `coerce_rule`

Automatic type coercions via built-in `coerce` symbol:

```
coerce_rule coerce Int Float $x |-> FloatOfInt $x;
coerce_rule coerce (List $a) (List $b) $l |-> map (lambda e, coerce $a $b e) $l;
```

**WARNING:** Experimental. `coerce ?1 Float t` won't reduce even if
`?1 === Int` registered. Unsafe with symbols reducing to protected symbols in RHS.

### 2.8 `unif_rule`

Guide unification with rewrite rules on `===` problems (matched modulo commutativity).
RHS-only variables become fresh metavars.

```
unif_rule Bool === T $t |-> [ $t === bool ];
unif_rule $x + $y === 0 |-> [ $x === 0; $y === 0 ];
```

**WARNING:** Experimental, no sanity checks.

### 2.9 `inductive`

Requires builtins `"Prop"` and `"P"`. Generates `ind_<name>` with rules.
Only strictly-positive types. Parameters implicit in constructor types.

```
inductive N : TYPE := | zero : N | succ : N -> N;
// Generates: constant symbol N, zero, succ; symbol ind_N; rules for ind_N
```

Parametrized and mutually recursive (with `with`):

```
(a:Set) inductive T: TYPE :=
| node: tau a -> F a -> T a
with F: TYPE :=
| nilF: F a
| consF: T a -> F a -> F a;   // use consF t l or @consF a t l
```

### 2.10 `opaque`

Set previously defined symbol as irreducible: `opaque f;`

---

## 3. Proof Mode

Enter with `symbol ... := begin` ... `end;`.
Goals: *typing* (`ctx |- ?M : T`) and *unification* (`ctx |- U === V`).
Tactics separated by `;`. Multiple subgoals enclosed in `{ ... }`:

```
opaque symbol thm : ... := begin
  refine ind ...
  { reflexivity }
  { assume x h; apply h }
end;
```

**Exit:** `end` (all solved), `abort` (no changes), `admitted` (axioms for remaining goals).

---

## 4. Tactics

All except `solve` apply to the focused (first) typing goal.

| Tactic | Effect |
|--------|--------|
| `admit` | add axioms proving focused goal |
| `apply t` | refine with `t _ ... _`; generates subgoals for each `Pi` argument |
| `assume h1 ... hn` | introduce `Pi` bindings into context |
| `change t` | replace goal `u` by `t` if `t === u` |
| `fail` | always fails (stop proof development) |
| `generalize y1` | move `y1` (and dependents) back into goal as `Pi` |
| `have x: t` | new subgoal for `t`, then prove original with `x: t` in context |
| `induction` | apply induction principle of inductive type in goal |
| `refine t` | instantiate goal by `t` (may contain `?n`, `_`); unsolved become goals |
| `remove h1 ... hn` | erase hypotheses (goal/remaining hyps must not depend on them) |
| `set x := t` | extend context with `x := t` |
| `simplify` | normalize goal (beta + rules). `simplify f`: unfold/apply rules for `f`. `simplify rule off`: beta only. Fails if no simplification. |
| `solve` | simplify all unification goals (only tactic applying to all goals) |
| `why3` / `why3 "P"` | call external prover (default Alt-Ergo). Needs `why3 config detect` first. |

**`why3` builtins:** `"T"`, `"P"`, `"bot"`, `"top"`, `"not"`, `"and"`, `"or"`, `"imp"`, `"eqv"`, `"all"`, `"ex"`

---

## 5. Equality Tactics

Require builtins `"T"`, `"P"`, `"eq"`, `"refl"`, `"eqind"`:

```
builtin "eq"    := ...  // : Pi [a], T a -> T a -> Prop
builtin "refl"  := ...  // : Pi [a] (x:T a), P(x = x)
builtin "eqind" := ...  // : Pi [a] x y, P(x = y) -> Pi p:T a -> Prop, P(p y) -> P(p x)
```

| Tactic | Effect |
|--------|--------|
| `reflexivity` | solve `Pi x1..xn, P(t = u)` when `t === u` |
| `symmetry` | replace `P(t = u)` by `P(u = t)` |
| `rewrite t` | given `t : Pi x1..xn, P(l = r)`, replace `l`-matches by `r` in goal |
| `rewrite left t` | rewrite right-to-left |

**Rewrite patterns** (SSReflect-style, after `.`):
`rewrite .[<pat>] t` where `<pat>` is: `<term>`, `in <term>`,
`in <id> in <term>`, `<id> in <term>`, `<term> in <id> in <term>`,
`<term> as <id> in <term>`.

---

## 6. Tacticals

| Tactical | Effect |
|----------|--------|
| `try T` | apply `T`; if fails, leave goal unchanged |
| `orelse T1 T2` | try `T1`, on failure try `T2` |
| `repeat T` | apply `T` repeatedly (stops if goal count decreases) |

### `eval`

`eval t` normalizes `t` and interprets result as reified tactic. Requires
tactic builtins (`"admit"`, `"and"` (= `;`), `"apply"`, `"assume"`,
`"fail"`, `"generalize"`, `"have"`, `"induction"`, `"orelse"`, `"refine"`,
`"reflexivity"`, `"remove"`, `"repeat"`, `"rewrite"`, `"set"`, `"simplify"`,
`"simplify rule off"`, `"solve"`, `"symmetry"`, `"try"`, `"why3"`).
String-taking tactics need `builtin "String"`.

```
symbol * : N -> Tactic -> Tactic; notation * infix 20;
rule 0 * _ |-> do_nothing with $n +1 * $t |-> $t & ($n * $t);
// eval 2 * #rewrite "" "" addnA & #reflexivity
```

---

## 7. Queries

Queries do not modify the environment.

| Query | Effect |
|-------|--------|
| `assert |- t : T;` | check typing |
| `assert ctx |- t : T;` | check typing in context |
| `assert |- t === u;` | check convertibility |
| `assertnot |- t === u;` | check non-convertibility |
| `compute t;` | print normal form |
| `type t;` | print type |
| `print f;` | info about symbol |
| `print unif_rule;` / `print coerce_rule;` | list rules |
| `print;` | list goals (proof mode) |
| `proofterm;` | print proof term (proof mode) |
| `flag "name" on/off;` | set flag (`flag;` alone lists flags) |
| `debug +ts;` / `debug -s;` | toggle debug flags (`debug;` alone lists them) |
| `verbose N;` | set verbosity (default 1) |
| `prover "name";` | set Why3 prover (default Alt-Ergo) |
| `prover_timeout N;` | set Why3 timeout in seconds (default 2) |
| `search <query>;` | search the index |

**Flags:** `"eta_equality"` (off), `"print_implicits"` (off),
`"print_contexts"` (off), `"print_domains"` (off), `"print_meta_args"` (off).

**Debug flags:** `a` metavars, `c` conversion, `d` decision trees,
`e` snf, `g` induction gen, `i` inference, `k` local confluence,
`l` library, `m` term building, `o` scoping, `p` pretty-print,
`r` rewrite, `s` subject-reduction, `t` tactics, `u` unification,
`v` inverse, `w` whnf, `x` export, `y` why3, `z` external tools.

### 7.1 Search Query Language

Queries against `~/.LPSearch.db` (from `index` command):

```
Q ::= B | Q "," Q | Q ";" Q | Q "|" PATH     // , (and) > ; (or) > | (path filter)
B ::= "name" "=" <uid>
    | <where> <rel> ["generalize"] <term>
    | "(" Q ")"
```

**Where:** `concl` | `hyp` | `spine` | `type` | `rule` | `lhs` | `rhs` | `anywhere` (only `>=`) | `name` (only `=`, no `generalize`)
**Rel:** `=` exact | `>` strict subterm | `>=` subterm-or-equal

Where semantics: `spine` = type minus conclusion; `concl` = innermost return type; `hyp` = argument types in spine.
Patterns can contain `_` (any term), `V#` (variable). `forall`/`->` usable for `Π`/`→`.

```
search hyp = (nat -> bool) , hyp >= (list nat);
search concl > plus | math.arithmetics;
```

---

## 8. Module System

One file = one module. Path derived from file path relative to library root.

**Library root** (in resolution order):
`--lib-root=DIR` > `$LAMBDAPI_LIB_ROOT/lib/lambdapi/lib_root` > `$OPAM_SWITCH_PREFIX/lib/lambdapi/lib_root` > `/usr/local/lib/lambdapi/lib_root`

**Package config** (`lambdapi.pkg` at project root, closest parent used):
```
package_name = my_package
root_path    = a.b.c        # ./foo/bar.lp -> a.b.c.foo.bar
```

**Dev mapping:** `--map-dir MOD:DIR`. **Conventions:** `std` = stdlib;
`libraries.<NAME>` = extracted libs. No package root path can prefix another's.

**Dedukti:** Can read `.dk`, translate via `export`. If both `file.dk`
and `file.lp` exist, `.lp` is used. `.lp` files can reference `.dk` symbols.

---

## 9. Command Line

```
lambdapi check [files]          # type-check
lambdapi parse [files]          # parse only
lambdapi export -o FMT file     # translate (lp/dk/raw_dk/hrs/xtc/raw_coq/stt_coq)
lambdapi lsp                    # LSP server
lambdapi init MOD_PATH          # new package (creates dir + lambdapi.pkg + Makefile)
lambdapi install [files]        # install under library root
lambdapi uninstall FILE         # uninstall package
lambdapi index [files]          # index symbols/rules -> ~/.LPSearch.db
lambdapi search "query"         # search index
lambdapi websearch              # web search server
lambdapi decision-tree MOD.SYM  # print decision tree (Dot)
lambdapi version / help
```

Input: `.lp` or `.dk` (auto-detected). `export` takes one file.
`parse`/`export`/`index` may compile dependencies if `.lpo` missing.
**Exit codes:** 0 ok, 123 error, 124 CLI error, 125 bug.

### 9.1 Common Flags

For `check`, `decision-tree`, `export`, `parse`, `lsp`:

| Flag | Effect |
|------|--------|
| `--lib-root=DIR` | set library root |
| `--map-dir=MOD:DIR` | map directory under module path |
| `-v N` / `--verbose=N` | verbosity (default 1; 0 = silent) |
| `--timeout=N` | timeout in seconds |
| `--no-sr-check` | disable subject-reduction check |
| `--no-colors` | disable ANSI colors |
| `-w` / `--no-warnings` | disable warnings |
| `--debug=FLAGS` | enable debug flags |
| `--record-time` | print timing stats (slower) |

### 9.2 Command-Specific Flags

**check:** `-c`/`--gen-obj` (generate `.lpo`), `--too-long=FLOAT` (warn slow commands, default inf)

**export:** `-o FMT` (format). `raw_dk`/`raw_coq`/`stt_coq` translate after parsing only (may be incomplete). `stt_coq` options: `--encoding LP_FILE` (mandatory; defines builtins `"Set"`, `"prop"`, `"arr"`, `"El"`, `"Prf"`, `"eq"`, `"not"`, `"imp"`, `"and"`, `"or"`, `"all"`, `"ex"`), `--no-implicits`, `--renaming LP_FILE`, `--requiring MODNAME`, `--mapping LP_FILE`, `--use-notations`

**index:** `--add` (append), `--rules LP_FILE` (normalize before indexing, repeatable), `--db FILE.db`

**search:** `--rules LP_FILE` (repeatable, use same as index), `--require FILE.lp`, `--db FILE.db`

**websearch:** `--port=N` (default 8080), `--rules LP_FILE`, `--require FILE.lp`, `--db FILE.db`, `--header FILE.html`, `--url STRING` (default empty; `**` = any)

**lsp:** `--standard-lsp`, `--log-file=FILE` (default `/tmp/lambdapi_lsp_log.txt`)

**decision-tree:** `--ghost` (internal symbols)

**install/uninstall:** `--dry-run`

**init:** `lambdapi init my_package` or `lambdapi init contrib.libs.my_pkg`

### 9.3 Confluence and Termination

```
--confluence=CMD   # HRS on stdin, output YES/NO/MAYBE
--termination=CMD  # XTC on stdin, output YES/NO/MAYBE
```

Tested: CSI^ho (`--confluence "csiho.sh --ext trs --stdin"`),
SizeChangeTool (`--termination "sct.native --no-color --stdin=xml"`).
Inspect: `--confluence "cat > output.trs; echo MAYBE"`.

---

## 10. BNF Grammar

```
<qid> ::= [<uid> "."]+ <uid>
<id>  ::= <uid> | <qid>

<command> ::= "opaque" <qid> ";"
  | "require" <qid>+ ";"
  | "require" [["private"] "open"] <qid>+ ";"
  | "require" <qid> "as" <uid> ";"
  | ["private"] "open" <qid>+ ";"
  | [<exposition>] <modifier>* "symbol" <uid> <param_list>*
      ":" <term> [<proof> | ":=" <term_proof>] ";"
  | [<exposition>] <modifier>* "symbol" <uid> <param_list>*
      ":=" <term> [<proof>] ";"
  | [<exposition>] <param_list>* "inductive" <inductive> ("with" <inductive>)* ";"
  | "rule" <rule> ("with" <rule>)* ";"
  | "builtin" <string> ":=" <id> ";"
  | "coerce_rule" <rule> ";"
  | "unif_rule" <unif_rule> ";"
  | "notation" <id> <notation> ";"
  | <query> ";"

<exposition> ::= "private" | "protected"
<side>       ::= "left" | "right"
<modifier>   ::= [<side>] "associative" | "commutative" | "constant"
               | "injective" | "opaque" | "sequential"

<inductive>   ::= <uid> <param_list>* ":" <term> ":=" ["|"] [<constructor> ("|" <constructor>)*]
<constructor> ::= <uid> <param_list>* ":" <term>
<rule>        ::= <term> "|>" <term>
<unif_rule>   ::= <equation> "|>" "[" <equation> (";" <equation>)* "]"
<equation>    ::= <term> "===" <term>

<notation> ::= "infix" [<side>] <float_or_int> | "postfix" <float_or_int>
             | "prefix" <float_or_int> | "quantifier"

<param_list> ::= <param> | "(" <param>+ ":" <term> ")" | "[" <param>+ [":" <term>] "]"
<param>      ::= <uid> | "_"

<term>        ::= <application> ["->" <term>] | [<application>] <bterm>
<application> ::= <head> <arg>*
<bterm>       ::= <binder> <abstraction>
                | "let" <uid> <param_list>* [":" <term>] ":=" <term> "in" <term>
<binder>      ::= "lambda" | "Pi" | "`" ["@"] <id>
<head>        ::= ["@"] <id> | "_" | "TYPE" | "?" <uid> [<env>]
                | "$" <uid> [<env>] | "(" <term> ")" | <integer> | <string>
<arg>         ::= <head> | "[" <term> "]"
<env>         ::= "." "[" [<term> (";" <term>)*] "]"
<abstraction> ::= <param_list>+ "," <term> | <param> ":" <term> "," <term>

<term_proof>  ::= <term> | <proof> | <term> <proof>
<proof>       ::= "begin" <subproof>+ <proof_end>
                | "begin" [<proof_steps>] <proof_end>
<subproof>    ::= "{" [<proof_steps>] "}"
<proof_steps> ::= <proof_step> [";"] | <proof_step> ";" <proof_steps>
<proof_step>  ::= <tactic> <subproof>*
<proof_end>   ::= "end" | "abort" | "admitted"

<tactic> ::= <query> | "admit" | "apply" <term> | "assume" <param>+
  | "change" <term> | "eval" <term> | "fail" | "generalize" <uid>
  | "have" <uid> ":" <term> | "induction" | "orelse" <tactic> <tactic>
  | "refine" <term> | "reflexivity" | "remove" <uid>+ | "repeat" <tactic>
  | "rewrite" [<side>] ["." "[" <rwpatt> "]"] <term>
  | "set" <uid> ":=" <term> | "simplify" | "simplify" <id>
  | "simplify" "rule" "off" | "solve" | "symmetry" | "try" <tactic>
  | "why3" [<string>]

<rwpatt> ::= <term> | "in" <term> | "in" <uid> "in" <term>
  | <term> "in" <term> ["in" <term>] | <term> "as" <uid> "in" <term>

<query> ::= <assert> <param_list>* "|-" <term> <test> <term>
  | "compute" <term> | "print" [<id> | "unif_rule" | "coerce_rule"]
  | "proofterm" | "debug" | "debug" ("+"|"-") <char>+
  | "flag" | "flag" <string> <switch> | "prover" <string>
  | "prover_timeout" <integer> | "verbose" <integer>
  | "type" <term> | "search" <search>

<assert> ::= "assert" | "assertnot"
<test>   ::= ":" | "==="
<switch> ::= "on" | "off"

<search>      ::= <disjunction> | <search> "|" <id>
<disjunction> ::= <conjunction> (";" <conjunction>)*
<conjunction> ::= <base> ("," <base>)*
<base> ::= "name" "=" <uid>
  | ("type"|"anywhere") ">=" ["generalize"] <term>
  | <where> <relation> ["generalize"] <term>
  | "(" <search> ")"
<where>    ::= "concl" | "hyp" | "spine" | "rule" | "lhs" | "rhs"
<relation> ::= "=" | ">" | ">="
```
