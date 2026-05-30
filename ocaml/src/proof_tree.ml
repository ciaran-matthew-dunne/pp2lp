(* Proof tree built from a replay.

   REPLAY output: regular sequent proof nodes are emitted prefix-style
   (rule before child subproofs), while branching quantifiers are split
   by their result-chain child:

     <Res child> ALL7 <Seq child>

   Inside result chains, primed rules are emitted after their children.
   Each Apply node carries the per-rule formula annotation from the
   replay (the goal PP saw when it applied that rule). *)

open Syntax_pp

type pp_tree =
  | Apply of {
      rule: string;
      arg: arg option;
      anno: rhs option;
      children: pp_tree list;
      (* For branching rules (ALL7/XST8): the FIN annotation that
         follows in the replay.  Records what `res_tm` the result
         chain produces — the term the continuation will see. *)
      fin_hint: rhs option;
    }

exception Bad_replay of string
exception Bad_replay_partial of string * pp_tree list

let bad fmt = Printf.ksprintf (fun s -> raise (Bad_replay s)) fmt

type mode = Seq_mode | Res_mode

let is_res_rule rule =
  rule = "STOP_1" || Rule_db.is_primed rule

let is_base_branch rule =
  (match Rule_db.base_of rule with
   | "ALL7" | "XST8" -> true
   | _ -> false)
  && not (is_res_rule rule)

let derivation_slots rule =
  Rule_db.slots rule
  |> List.filter_map (function
    | Rule_db.Con -> None
    | Rule_db.Seq -> Some Seq_mode
    | Rule_db.Res -> Some Res_mode)

let child_modes mode rule =
  let slots = derivation_slots rule in
  if mode = Res_mode || is_res_rule rule then
    List.map (fun _ -> Res_mode) slots
  else
    slots

let mode_name = function
  | Seq_mode -> "sequent"
  | Res_mode -> "result-chain"

let debug_replay =
  match Sys.getenv_opt "PP2LP_DEBUG_REPLAY" with
  | Some ("1" | "true" | "yes") -> true
  | _ -> false

let debug_replayf fmt =
  Printf.ksprintf
    (fun s -> if debug_replay then Printf.eprintf "%s\n%!" s)
    fmt

let line_rule ((rule, _), _) = rule

let rec skip_phantoms = function
  | (((rule, _), _) :: rest) when Rule_db.is_phantom rule ->
    skip_phantoms rest
  | lines -> lines

let make_node ?(fin_hint=None) rule arg anno children =
  Apply { rule; arg; anno = Some anno; children; fin_hint }

let pop_res rule stack =
  match stack with
  | [] ->
    raise (Bad_replay_partial
             (Printf.sprintf "%s expected a result-chain child but stack is empty"
                rule,
              []))
  | x :: rest -> x, rest

let pop_res_children rule modes stack =
  let rec go acc stack = function
    | [] -> acc, stack
    | Res_mode :: rest ->
      let child, stack = pop_res rule stack in
      go (child :: acc) stack rest
    | Seq_mode :: _ ->
      bad "%s: internal error: sequent slot in result-chain stack" rule
  in
  go [] stack (List.rev modes)

let rec parse_prefix mode lines =
  match skip_phantoms lines with
  | [] -> bad "unexpected end of replay while reading a %s proof"
            (mode_name mode)
  | ((rule, arg), anno) :: rest ->
    debug_replayf "parse_prefix %s: %s" (mode_name mode) rule;
    if mode = Seq_mode && is_res_rule rule then
      parse_branch_seq lines
    else if mode = Seq_mode && is_base_branch rule then
      bad "%s appeared before its result-chain child in replay" rule
    else if mode = Res_mode && is_res_rule rule && Rule_db.rule_arity rule > 0 then
      bad "%s appeared before its result-chain children in replay" rule
    else
      let modes = child_modes mode rule in
      let children, rest = parse_prefix_children rest modes in
      make_node rule arg anno children, rest

and parse_prefix_children lines = function
  | [] -> [], lines
  | mode :: modes ->
    let child, lines = parse_prefix mode lines in
    let children, lines = parse_prefix_children lines modes in
    child :: children, lines

and parse_branch_seq lines =
  debug_replayf "parse_branch_seq";
  let chain, lines = parse_res_until_base_branch [] lines in
  match skip_phantoms lines with
  | (((rule, arg), anno) :: rest) when is_base_branch rule ->
    if skip_phantoms rest = [] then
      bad "%s replay branch has no sequent continuation after its result-chain"
        rule;
    (* The first FIN after a branching rule describes the `res_tm` the
       chain supplies — the form the continuation will work with via
       the res_eq equality.  Capture for tree-display purposes. *)
    let fin_hint = match rest with
      | (((r, _), fin_anno) :: _) when r = "FIN" -> Some fin_anno
      | _ -> None
    in
    let cont, rest = parse_prefix Seq_mode rest in
    make_node ~fin_hint rule arg anno [chain; cont], rest
  | [] ->
    bad "result-chain proof was not followed by ALL7/XST8 in replay"
  | line :: _ ->
    bad "result-chain proof was followed by %s, expected ALL7/XST8"
      (line_rule line)

and parse_res_until_base_branch stack lines =
  match skip_phantoms lines with
  | [] ->
    (match stack with
     | [root] -> root, []
     | [] -> bad "empty result-chain proof in replay"
     | xs ->
       raise (Bad_replay_partial
                (Printf.sprintf
                   "result-chain replay ended with %d nodes on stack"
                   (List.length xs),
                 xs)))
  | (((rule, _), _) :: _) as lines when is_base_branch rule ->
    debug_replayf "parse_res stop at %s with %d stack nodes"
      rule (List.length stack);
    (match stack with
     | [root] -> root, lines
     | [] ->
       bad "%s expected a result-chain child but none was parsed" rule
     | xs ->
       raise (Bad_replay_partial
                (Printf.sprintf
                   "%s reached with %d result-chain nodes on stack (expected 1)"
                   rule (List.length xs),
                 xs)))
  | ((rule, arg), anno) :: rest when is_res_rule rule ->
    debug_replayf "parse_res postfix %s with %d stack nodes"
      rule (List.length stack);
    let modes = child_modes Res_mode rule in
    let children, stack = pop_res_children rule modes stack in
    let node = make_node rule arg anno children in
    parse_res_until_base_branch (node :: stack) rest
  | lines ->
    (match lines with
     | ((rule, _), _) :: _ ->
       debug_replayf "parse_res prefix-as-res %s with %d stack nodes"
         rule (List.length stack)
     | [] -> ());
    let node, rest = parse_prefix Res_mode lines in
    parse_res_until_base_branch (node :: stack) rest

let build_replay (rules : (lhs * rhs) list) : pp_tree =
  let root, rest = parse_prefix Seq_mode rules in
  match skip_phantoms rest with
  | [] -> root
  | xs ->
    raise (Bad_replay_partial
             (Printf.sprintf "replay left %d unconsumed rule lines"
                (List.length xs),
              []))

let build = build_replay

let rule_of     (Apply { rule; _ })     = rule
let arg_of      (Apply { arg; _ })      = arg
let anno_of     (Apply { anno; _ })     = anno
let children_of (Apply { children; _ }) = children

let debug = ref false

(* Render an annotation: the goal at this point in the proof. *)
let rhs_to_pp = function
  | Simple p -> Emit_pp.prd_to_pp p
  | Fin (norm, _, _, _) -> Printf.sprintf "FIN→ %s" (Emit_pp.prd_to_pp norm)

(* Like rhs_to_pp but strips the "FIN→ " prefix from FIN annotations —
   used when composing equalities from FIN-supplied terms. *)
let rhs_to_term = function
  | Simple p -> Emit_pp.prd_to_pp p
  | Fin (norm, _, _, _) -> Emit_pp.prd_to_pp norm

(* Label a child by its parent's slot kind.  Both labels use the same
   trailing-parens style: `(equality)` for the result chain (its node
   is the equality it derives), `(continuation)` for the sequent
   subproof. *)
let child_label_for parent_rule i =
  let slots = Rule_db.slots parent_rule in
  if not (Rule_db.is_branching parent_rule) then ""
  else match List.nth_opt slots i with
  | Some Rule_db.Res -> " (equality)"
  | Some Rule_db.Seq -> " (continuation)"
  | _ -> ""

(* Extract a node's annotation as a printable goal. *)
let node_goal = function
  | Apply { anno = Some r; _ } -> rhs_to_term r
  | Apply { anno = None; _ } -> "?"

(* Render a node as a flat Lisp-style proof term — the whole result
   chain collapsed into one expression.  Arguments are dropped. *)
let rec render_term = function
  | Apply { rule; children; _ } ->
    if children = [] then rule
    else
      let children_s =
        List.map render_term children |> String.concat " "
      in
      Printf.sprintf "(%s %s)" rule children_s

(* Tree visualization: nodes are GOALS; rules label the arrows.
   Each node prints:
     <prefix> goal
     <indent>  | rule(arg)        ← the rule applied to this goal
   Children render below as subgoals.
   For a result-chain child of a branching rule (ALL7/XST8), its
   "goal" is the equality `<chain top> = <res_tm>` — the equality the
   chain derives for use by the continuation. *)
let rec pp_tree ?(indent="") ?(last=true) ?(child_label="") ch node =
  let prefix = if last then "+-- " else "|-- " in
  let child_indent = indent ^ (if last then "    " else "|   ") in
  match node with
  | Apply { rule; anno; children; fin_hint; _ } ->
    let goal_s = match anno with
      | None -> "(no annotation)"
      | Some r -> rhs_to_pp r
    in
    (* Goal node: `+-- goal (label)`.
       Edge (rule applied here, points down to children): `rule ↓`.
       Proof term (for collapsed result chains, proves goal above): `(term) ⊢`. *)
    Printf.fprintf ch "%s%s%s%s\n" indent prefix goal_s child_label;
    Printf.fprintf ch "%s%s ↓\n" child_indent rule;
    let n = List.length children in
    List.iteri (fun i c ->
      let is_result_chain = i = 0 && Rule_db.is_branching rule in
      let label = child_label_for rule i in
      if is_result_chain then begin
        (* Result chain: one node for the equality, one node for the
           proof term that derives it. *)
        let last_child = i = n - 1 in
        let inner_prefix = if last_child then "+-- " else "|-- " in
        let inner_indent = child_indent ^ (if last_child then "    " else "|   ") in
        let eq_goal = match fin_hint with
          | Some fin_anno ->
            Printf.sprintf "%s = %s" (node_goal c) (rhs_to_term fin_anno)
          | None -> node_goal c
        in
        Printf.fprintf ch "%s%s%s%s\n" child_indent inner_prefix eq_goal label;
        Printf.fprintf ch "%s+-- %s\n" inner_indent (render_term c)
      end else
        pp_tree ~indent:child_indent ~last:(i = n - 1) ~child_label:label ch c
    ) children

let debug_tree label node =
  if !debug then begin
    Printf.eprintf "=== %s ===\n" label;
    pp_tree ~indent:"" ~last:true stderr node
  end
