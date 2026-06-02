open Syntax_pp

type binder_ty = Tau_i

type term =
  | Hole
  | Trust
  | Name of string
  | Exp of exp
  | Pred of prd
  | App of string * term list
  | Lambda of string * binder_ty option * term
  | Raw of string

(* Provenance: where an emitted tactic came from in the replay.
   `rule` is the PP rule, `replay_line` its 1-indexed line in the
   .replay file, `goal` the per-rule annotation (the goal PP saw).
   Carried by [Commented]; the pretty-printer records the emitted line of
   each into a sink so the CLI can build a side-channel line→rule map.
   No comments are written into the generated Lambdapi. *)
type prov = { rule : string; replay_line : int; goal : string }

type tactic =
  | Refine of string * term list
  | Rewrite of { try_ : bool; rtl : bool; name : string }

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

let rec pp_term buf = function
  | Hole -> Buffer.add_char buf '_'
  | Trust -> Buffer.add_string buf "trust"
  | Name name -> Buffer.add_string buf name
  | Exp e ->
    Buffer.add_char buf '(';
    Pp_lp.pp_exp buf e;
    Buffer.add_char buf ')'
  | Pred p ->
    Buffer.add_char buf '(';
    Pp_lp.pp_prd buf p;
    Buffer.add_char buf ')'
  | App (name, args) ->
    Buffer.add_char buf '(';
    Buffer.add_string buf name;
    List.iter (fun arg ->
      Buffer.add_char buf ' ';
      pp_term buf arg) args;
    Buffer.add_char buf ')'
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
  | Raw s -> Buffer.add_string buf s

let pp_tactic buf = function
  | Refine (rule, args) ->
    Buffer.add_string buf "refine ";
    Buffer.add_string buf rule;
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
