(* How a PP variable bound by an enclosing compound (n-ary) binder renders —
   defined in [Pp_lp] (the rendering layer) and re-exported here, with its
   constructor, so proof-side modules building envs can say [L.Proj].
   [Proj (slot, tuple-var)] renders the infix `tuple-var ⋕ slot` (the binder
   introduced a `Tuple n` value under [tuple-var]).  Carried on [Pred]/[Exp] so
   the formula is rendered the right way at print time, not pre-rendered to a
   string. *)
type proj_binding = Pp_lp.proj_binding =
  | Proj of int * string
type proj_env = Pp_lp.proj_env

(* `Pi_pred` annotates a λ-binder with `π (<pred>)` — used when the bound
   proof's type must be pinned explicitly (a metavariable-headed application
   would otherwise leave the subgoal's type undetermined, e.g. EGALITE's
   `refine (λ k : π G, k ev…) _`). *)
type binder_ty = Tau_i | Pi_pred of proj_env * Syntax_pp.prd

(* A Lambdapi term argument.  Fully structured — there is no string escape
   hatch.  A PP formula is carried as [Pred]/[Exp] with its [proj_env] and
   handed to [Pp_lp] only when the printer runs. *)
type term =
  | Hole
  | Name of string                    (* an LP identifier *)
  | App of term * term list           (* application (f a b …), parenthesised *)
  | Expl of term                      (* @t — pass implicit arguments explicitly *)
  | Lambda of string * binder_ty option * term
  | Eq of term * term                 (* LP-level equality a = b *)
  | Infix of string * term * term     (* an infix application `(a op b)` — needed
                                         where a notation-infix symbol (`+`) must
                                         print infix, e.g. inside a `rewrite .[…]`
                                         pattern (the matcher rejects prefix `(+ a b)`) *)
  | Pred of proj_env * Syntax_pp.prd  (* a PP predicate, LP-encoded at print time *)
  | Exp of proj_env * Syntax_pp.exp   (* a PP expression, LP-encoded at print time *)

(* Provenance: where an emitted tactic came from in the replay.
   `rule` is the PP rule, `replay_line` its 1-indexed line in the
   .replay file, `goal` the per-rule annotation (the goal PP saw).
   Carried by [Commented]; the pretty-printer records the emitted line of
   each into a sink so the CLI can build a side-channel line→rule map.
   No comments are written into the generated Lambdapi. *)
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
  (* Attach provenance to the first emitted line of the wrapped script.
     Exactly one per proof-tree node (its primary tactic). *)
  | Commented of prov * t

let pp_binder_ty buf = function
  | Tau_i -> Buffer.add_string buf "\xcf\x84 \xce\xb9" (* τ ι *)
  | Pi_pred (env, p) ->
    Buffer.add_string buf "\xcf\x80 ("; (* π *)
    Pp_lp.pp_prd ~env buf p;
    Buffer.add_char buf ')'

let rec pp_term buf = function
  | Hole -> Buffer.add_char buf '_'
  | Name name -> Buffer.add_string buf name
  | App (head, args) ->
    Buffer.add_char buf '(';
    pp_term buf head;
    List.iter (fun arg ->
      Buffer.add_char buf ' ';
      pp_term buf arg) args;
    Buffer.add_char buf ')'
  | Expl t ->
    Buffer.add_char buf '@';
    pp_term buf t
  | Lambda (name, ty, body) ->
    Buffer.add_string buf "(\xce\xbb "; (* λ *)
    Buffer.add_string buf name;
    (match ty with
     | None -> ()
     | Some ty ->
       Buffer.add_string buf " : ";
       pp_binder_ty buf ty);
    Buffer.add_string buf ", ";
    pp_term buf body;
    Buffer.add_char buf ')'
  | Eq (a, b) ->
    Buffer.add_char buf '(';
    pp_term buf a;
    Buffer.add_string buf " = ";
    pp_term buf b;
    Buffer.add_char buf ')'
  | Infix (op, a, b) ->
    Buffer.add_char buf '(';
    pp_term buf a;
    Buffer.add_char buf ' ';
    Buffer.add_string buf op;
    Buffer.add_char buf ' ';
    pp_term buf b;
    Buffer.add_char buf ')'
  | Pred (env, p) ->
    Buffer.add_char buf '(';
    Pp_lp.pp_prd ~env buf p;
    Buffer.add_char buf ')'
  | Exp (env, e) ->
    Buffer.add_char buf '(';
    Pp_lp.pp_exp ~env buf e;
    Buffer.add_char buf ')'

let pp_tactic buf = function
  | Refine (head, args) ->
    Buffer.add_string buf "refine ";
    pp_term buf head;
    List.iter (fun arg ->
      Buffer.add_char buf ' ';
      pp_term buf arg) args
  | Rewrite { try_; rtl; name } ->
    if try_ then Buffer.add_string buf "try ";
    Buffer.add_string buf "rewrite ";
    if rtl then Buffer.add_string buf "left ";
    Buffer.add_string buf name

let count_nl s =
  let n = ref 0 in
  String.iter (fun c -> if c = '\n' then incr n) s;
  !n

(* `lead_pad` is written before the first line; subsequent lines use `pad`.
   Inside `{ ... }`, callers pass `lead_pad = ""` so the first tactic sits
   flush against the brace.  `sink`, when given, collects `(emitted 1-based
   line, provenance)` for each [Commented] node so the CLI can build a
   side-channel line→rule map — NO comments are written into the output. *)
let rec pp ?(pad = "") ?lead_pad ?sink buf t =
  let lead_pad = match lead_pad with Some s -> s | None -> pad in
  match t with
  | Step tactic ->
    Buffer.add_string buf lead_pad;
    pp_tactic buf tactic
  | Then (tactic, next) ->
    Buffer.add_string buf lead_pad;
    pp_tactic buf tactic;
    Buffer.add_string buf ";\n";
    pp ~pad ?sink buf next
  | Assume (name, next) ->
    Buffer.add_string buf lead_pad;
    Buffer.add_string buf "assume ";
    Buffer.add_string buf name;
    Buffer.add_string buf ";\n";
    pp ~pad ?sink buf next
  | Assume_then (tactic, name, next) ->
    Buffer.add_string buf lead_pad;
    pp_tactic buf tactic;
    Buffer.add_string buf ";\n";
    Buffer.add_string buf pad;
    Buffer.add_string buf "assume ";
    Buffer.add_string buf name;
    Buffer.add_string buf ";\n";
    pp ~pad ?sink buf next
  | Branches (tactic, left, right) ->
    Buffer.add_string buf lead_pad;
    pp_tactic buf tactic;
    Buffer.add_char buf '\n';
    let inner = pad ^ "  " in
    Buffer.add_string buf pad;
    Buffer.add_string buf "{ ";
    pp ~pad:inner ~lead_pad:"" ?sink buf left;
    Buffer.add_string buf " }\n";
    Buffer.add_string buf pad;
    Buffer.add_string buf "{ ";
    pp ~pad:inner ~lead_pad:"" ?sink buf right;
    Buffer.add_string buf " }"
  | Commented (prov, inner) ->
    (* Record where this node's primary tactic lands (1-based line in `buf`),
       then render the tactic plainly — no comment in the output. *)
    (match sink with
     | Some s -> s := (1 + count_nl (Buffer.contents buf), prov) :: !s
     | None -> ());
    pp ~pad ~lead_pad ?sink buf inner
