(* Lambdapi tactic-script AST and its pretty-printer.  The generated `.lp`
   carries no comments; provenance is recorded out-of-band via the [sink]
   so the CLI can map an error line back to the rule that produced it.

   Terms are fully structured — there is no string escape hatch.  A PP
   formula argument is carried as [Pred]/[Exp] together with the projection
   environment ([proj_env]) it must be rendered under, and is turned into
   Lambdapi concrete syntax by [Pp_lp] at print time, not before. *)

(* How a PP variable bound by an enclosing compound (n-ary) binder renders —
   [Pp_lp.proj_binding] re-exported with its constructor so proof-side env
   builders can write [Proj].  [Proj (slot, tuple-var)] → the infix
   `tuple-var ⋕ slot`. *)
type proj_binding = Pp_lp.proj_binding =
  | Proj of int * string
type proj_env = Pp_lp.proj_env

(* `Pi_pred` annotates a λ-binder with `π (<pred>)` — pins the bound proof's
   type when a metavariable-headed application would leave it undetermined. *)
type binder_ty = Tau_i | Pi_pred of proj_env * Syntax_pp.prd

type term =
  | Hole
  | Name of string                    (* an LP identifier *)
  | App of term * term list           (* application (f a b …), parenthesised *)
  | Expl of term                      (* @t — pass implicit arguments explicitly *)
  | Lambda of string * binder_ty option * term
  | Eq of term * term                 (* LP-level equality a = b *)
  | Infix of string * term * term     (* infix application `(a op b)` — for a
                                         notation-infix symbol that must print
                                         infix (e.g. the list cons `⸬` in ρ) *)
  | Pred of proj_env * Syntax_pp.prd  (* a PP predicate, LP-encoded at print time *)
  | Exp of proj_env * Syntax_pp.exp   (* a PP expression, LP-encoded at print time *)

(* Where an emitted tactic came from in the replay: the PP [rule], its
   1-indexed [replay_line], and the [goal] PP saw (its annotation). *)
type prov = { rule : string; replay_line : int; goal : string }

type tactic =
  | Refine of term * term list        (* refine head args — head is [Name]/[Expl] *)
  | Rewrite of { try_ : bool; rtl : bool; name : string }
    (* a rewrite by a named lemma; [try_] prefixes `try`, [rtl] `left` *)

type t =
  | Step of tactic
  | Then of tactic * t
  | Assume of string * t
  | Assume_then of tactic * string * t
  | Branches of tactic * t * t
  | Commented of prov * t

(* Render [t] into [buf].  [pad] indents every line; [lead_pad] overrides
   the first line's indent (callers inside `{ … }` pass ""); [sink], when
   given, collects (emitted 1-based line, provenance) for each [Commented]
   node — no comment is written into the output. *)
val pp :
  ?pad:string -> ?lead_pad:string -> ?sink:(int * prov) list ref ->
  Buffer.t -> t -> unit
