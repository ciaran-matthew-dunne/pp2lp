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
      (* 1-indexed line in the .replay file this node's rule came from,
         carried for provenance comments in the emitted Lambdapi. *)
      src_line: int;
    }

exception Bad_replay of string

let bad fmt = Printf.ksprintf (fun s -> raise (Bad_replay s)) fmt

type mode = Seq_mode | Res_mode

let is_res_rule rule =
  rule = "STOP_1" || Rule_db.is_primed rule

(* A "base branch" is a branching rule (one with a Res slot — ALL7/XST8)
   in its un-primed form.  Derived from rule_db's slot metadata rather
   than hard-coding the rule names. *)
let is_base_branch rule =
  Rule_db.is_branching rule && not (is_res_rule rule)

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

let line_rule ((rule, _), _, _) = rule

let rec skip_phantoms = function
  | (((rule, _), _, _) :: rest) when Rule_db.is_phantom rule ->
    skip_phantoms rest
  | lines -> lines

let make_node ~src_line rule arg anno children =
  Apply { rule; arg; anno = Some anno; children; src_line }

let pop_res rule stack =
  match stack with
  | [] ->
    (* A well-formed result chain always carries one sub-result per child slot
       of every combine rule (arities are correct — e.g. OR3/ALL7/XST8 = 2), so
       an empty stack here means REPLAY dropped result-chain nodes when
       serialising the .trace.  Verified across the apero corpus: every such
       failure has strictly fewer chain nodes in the .replay than in the
       .trace.  Phrase it as truncation so `pp2lp gen` drops the benchmark
       (classify_error → E_REPLAY_TRUNCATED), same as the leaf-missing case. *)
    bad "%s result-chain child missing (stack empty) — REPLAY truncated the chain"
      rule
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
  | ((rule, arg), anno, line) :: rest ->
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
      make_node ~src_line:line rule arg anno children, rest

and parse_prefix_children lines = function
  | [] -> [], lines
  | mode :: modes ->
    let child, lines =
      if mode = Res_mode then
        parse_one_res_tree lines
      else
        parse_prefix mode lines
    in
    let children, lines = parse_prefix_children lines modes in
    child :: children, lines

and parse_one_res_tree lines =
  parse_res_tree_stack [] lines

and parse_res_tree_stack stack lines =
  match skip_phantoms lines with
  | [] ->
    (match stack with
     | [root] -> root, []
     | _ -> bad "unexpected end of result-chain child proof")
  | (((rule, _), _, _) :: _) as lines when is_base_branch rule ->
    (match stack with
     | [root] -> root, lines
     | _ -> bad "base branch reached but result-chain child stack is invalid")
  | ((rule, arg), anno, line) :: rest when is_res_rule rule ->
    let arity = Rule_db.rule_arity rule in
    if arity > List.length stack then
      (match stack with
       | [root] -> root, lines
       | _ -> bad "postfix rule %s cannot be applied, stack size is %d" rule (List.length stack))
    else
      let modes = child_modes Res_mode rule in
      let children, stack = pop_res_children rule modes stack in
      let node = make_node ~src_line:line rule arg anno children in
      parse_res_tree_stack (node :: stack) rest
  | lines ->
    let node, rest = parse_prefix Res_mode lines in
    parse_res_tree_stack (node :: stack) rest

and parse_branch_seq lines =
  debug_replayf "parse_branch_seq";
  let chain, lines = parse_res_until_base_branch [] lines in
  match skip_phantoms lines with
  | (((rule, arg), anno, line) :: rest) when is_base_branch rule ->
    if skip_phantoms rest = [] then
      bad "%s replay branch has no sequent continuation after its result-chain"
        rule;
    let cont, rest = parse_prefix Seq_mode rest in
    make_node ~src_line:line rule arg anno [chain; cont], rest
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
       bad "result-chain replay ended with %d nodes on stack" (List.length xs))
  | (((rule, _), _, _) :: _) as lines when is_base_branch rule ->
    debug_replayf "parse_res stop at %s with %d stack nodes"
      rule (List.length stack);
    (match stack with
     | [root] -> root, lines
     | [] ->
       bad "%s expected a result-chain child but none was parsed" rule
     | xs ->
       bad "%s reached with %d result-chain nodes on stack (expected 1)"
         rule (List.length xs))
  | ((rule, _), _, _) :: _ when stack = [] && is_res_rule rule
                                && Rule_db.rule_arity rule > 0 ->
    (* A well-formed result chain always begins with a leaf (STOP_1, a 0-ary
       node, or a prefix subtree) to seed the stack.  If the very first node is
       a postfix rule that needs children, the leaf subtree was dropped — this
       is the REPLAY tool truncating the chain (it emits e.g. [AR12_1 AXM3_1
       AXM3_1 AND4_1] before [IMP4_1 AR7_1 …] in the .trace but omits them from
       the .replay).  Flag it as truncation so `pp2lp gen` drops the benchmark,
       same as the dropped-continuation case — it can't be emitted. *)
    bad "result-chain leaf missing before %s — REPLAY truncated the chain" rule
  | ((rule, arg), anno, line) :: rest when is_res_rule rule ->
    debug_replayf "parse_res postfix %s with %d stack nodes"
      rule (List.length stack);
    let modes = child_modes Res_mode rule in
    let children, stack = pop_res_children rule modes stack in
    let node = make_node ~src_line:line rule arg anno children in
    parse_res_until_base_branch (node :: stack) rest
  | lines ->
    (match lines with
     | ((rule, _), _, _) :: _ ->
       debug_replayf "parse_res prefix-as-res %s with %d stack nodes"
         rule (List.length stack)
     | [] -> ());
    let node, rest = parse_prefix Res_mode lines in
    parse_res_until_base_branch (node :: stack) rest

let build_replay (rules : (lhs * rhs * int) list) : pp_tree =
  let root, rest = parse_prefix Seq_mode rules in
  match skip_phantoms rest with
  | [] -> root
  | xs ->
    bad "replay left %d unconsumed rule lines" (List.length xs)

let build = build_replay

let anno_of (Apply { anno; _ }) = anno
