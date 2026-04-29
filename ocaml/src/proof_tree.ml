open Syntax_pp

type proof_node =
  | Apply of {
      rule: string;
      arg: arg option;
      goal: prd;
      children: proof_node list;
    }

(* --- Exceptions --- *)

exception Ill_formed_replay of string
exception Emit_admit of string

(* --- Rule name predicates --- *)

(** A _1-suffixed rule: part of an equality chain (primed derivation).
    These appear in replays as literal _1 names (STOP_1, IMP4_1, etc.)
    and only occur as children of branching quantifier nodes. *)
let is_primed_rule = Rule_db.is_primed_name

(** ALL7/XST8: branching quantifiers.
    First child is an equality chain (_1 rules, built postorder).
    Second child is a normal subtree (built preorder). *)
let is_branching_quantifier = Rule_db.is_branching

(** NRM with a digit suffix: NRM1, NRM3, etc.
    NOT the bare "NRM" phantom (arity -1). *)
let is_nrm_step = Rule_db.is_nrm_step

(* --- Replay arity --- *)

(** Arity of a rule as it appears in the replay.
    For _1-suffixed rules, strip the suffix and look up the base:
      IMP4_1 → IMP4 → 1, AND1_1 → AND1 → 2, etc.
    STOP_1 is special: STOP has arity 1 (it carries the leaf goal as a
    child in the main tree), but inside the _1 equality chain STOP_1 is
    the seed leaf — arity 0.
    Any lookup miss is surfaced as Ill_formed_replay, not a raw Failure. *)
let replay_arity name =
  if name = "STOP_1" then 0
  else
    let base =
      if is_primed_rule name
      then String.sub name 0 (String.length name - 2)
      else name
    in
    try Rule_db.rule_arity base
    with Failure _ ->
      raise (Ill_formed_replay
        (Printf.sprintf "unknown rule %S in replay" name))

(* --- Helpers --- *)

let goal_of_rhs = function
  | Simple p -> p
  | Fin (p, _, _, _) -> p

(** Collect the equality chain (primed prefix) preceding a branching
    quantifier.  Scans forward from [pos] through _1-suffixed rules
    until an ALL7/XST8 is found.

    Returns [Some (collected_lines, branch_pos)] where
    - [collected_lines]: the _1 lines forming the equality derivation
    - [branch_pos]: index of the ALL7/XST8 that consumes the chain

    Skipped during collection (not proof steps):
    - Non-_1 NRM steps (NRM1, NRM3 …): normalisation bookkeeping
      that PP uses to compute the FIN result
    - Non-FIN phantoms (STOP_NORM, bare NRM)

    FIN lines are kept: they carry the result predicate that
    [build_postorder] threads to the enclosing branching quant via
    [last_fin]. *)
let rec collect_primed arr n pos =
  if pos >= n then None
  else
    let ((name, _), rhs) = arr.(pos) in
    if is_branching_quantifier name then
      Some ([], pos)
    else if replay_arity name = -1 then begin
      (* Phantom. FIN lines inside a primed chain signal a completed
         inner branching quantifier (nested ALL7/XST8 inside an outer
         one); we keep them in the collected list so build_postorder
         can thread last_fin to the inner branching node. Non-FIN
         phantoms (STOP_NORM, bare NRM) carry nothing and are dropped. *)
      match rhs with
      | Fin _ ->
        (match collect_primed arr n (pos + 1) with
         | Some (rest, bp) -> Some (arr.(pos) :: rest, bp)
         | None -> None)
      | _ -> collect_primed arr n (pos + 1)
    end
    else if is_nrm_step name && not (is_primed_rule name) then
      (* Non-_1 NRM step: normalisation bookkeeping, skip *)
      collect_primed arr n (pos + 1)
    else
      match collect_primed arr n (pos + 1) with
      | Some (rest, branch_pos) -> Some (arr.(pos) :: rest, branch_pos)
      | None -> None

(* --- Debug output --- *)

let debug = ref false

let rec pp_tree ?(indent="") ?(last=true) ch node =
  let prefix = if last then "└── " else "├── " in
  let child_indent = indent ^ (if last then "    " else "│   ") in
  match node with
  | Apply { rule; goal; children; _ } ->
    Printf.fprintf ch "%s%s%s  <%s>\n" indent prefix rule
      (Emit_pp.prd_to_pp goal);
    let n = List.length children in
    List.iteri (fun i c ->
      pp_tree ~indent:child_indent ~last:(i = n - 1) ch c
    ) children

let debug_tree label node =
  if !debug then begin
    Printf.eprintf "=== %s ===\n" label;
    pp_tree ~indent:"" ~last:true stderr node
  end

(** Build a proof subtree from the _1 equality chain.

    PP emits equality-chain rules in {b postorder} (leaves first):

    {v
    [STOP_1]  <p>                 ← leaf (arity 0)
    [IMP4_1]  <q ⇒ p>            ← pops 1, pushes parent
    [AND3_1]  <q ∧ r ⇒ p>        ← pops 1, pushes parent
    v}

    Stack-based evaluation (like a postfix calculator):
    - Arity 0 (STOP_1): push a leaf
    - Arity 1 (IMP4_1, AND3_1 …): pop one child, push parent
    - Arity 2 (AND1_1, OR3_1 …): pop two children, push parent
    - Phantom (FIN): track the result predicate, don't push

    After processing all lines, the stack should hold exactly one root.
    Non-_1 NRM steps must already have been filtered by the caller
    (this is what [collect_primed] does). *)
let build_postorder (lines : line list) : proof_node =
  let stack = ref [] in
  let last_fin = ref None in
  let push node = stack := node :: !stack in
  let pop rule_name =
    match !stack with
    | [] ->
      raise (Ill_formed_replay
        (Printf.sprintf "build_postorder: empty stack at %s" rule_name))
    | x :: rest -> stack := rest; x
  in
  List.iter (fun ((rule_name, arg), rhs) ->
    let goal = goal_of_rhs rhs in
    let arity = replay_arity rule_name in
    if arity = -1 then begin
      (* Track FIN results for the enclosing branching quantifier *)
      match rhs with
      | Fin (p, _, _, _) -> last_fin := Some (Pred p)
      | _ -> ()
    end
    else begin
      let arg =
        if is_branching_quantifier rule_name then
          (match !last_fin with
           | Some _ as f -> last_fin := None; f
           | None -> arg)
        else arg
      in
      if arity = 0 then
        push (Apply { rule = rule_name; arg; goal; children = [] })
      else if arity = 1 then
        let child = pop rule_name in
        push (Apply { rule = rule_name; arg; goal; children = [child] })
      else begin
        let child2 = pop rule_name in
        let child1 = pop rule_name in
        push (Apply { rule = rule_name; arg; goal;
                      children = [child1; child2] })
      end
    end
  ) lines;
  match !stack with
  | [root] ->
    debug_tree "result derivation (postorder)" root;
    root
  | [] -> raise (Ill_formed_replay "build_postorder: no nodes produced")
  | nodes ->
    raise (Ill_formed_replay
      (Printf.sprintf "build_postorder: %d nodes remain on stack"
         (List.length nodes)))

(** Skip phantom lines (FIN, STOP_NORM, NRM) for position tracking.
    The caller extracts FIN data before calling this. *)
let rec skip_phantoms arr n pos =
  if pos >= n then pos
  else
    let ((name, _), _) = arr.(pos) in
    if replay_arity name = -1
    then skip_phantoms arr n (pos + 1)
    else pos

(** Skip a FIN line and any trailing phantoms. *)
let skip_fin arr n pos =
  if pos >= n then pos
  else
    let ((name, _), _) = arr.(pos) in
    if name = "FIN" then skip_phantoms arr n (pos + 1)
    else pos

(* --- Main tree builder --- *)

(** Build a proof tree from replay lines.

    The main replay is {b preorder} (parent first, children after):

    {v
    [IMP4]    <p ⇒ q>            ← parent (arity 1)
    [AXM3]    <q>                 ← child
    v}

    The one exception is the equality chain (_1 rules) preceding a
    branching quantifier (ALL7/XST8).  These appear in postorder and
    are handled by [collect_primed] + [build_postorder].

    Raises [Ill_formed_replay] on truncated or malformed replays. *)
let build (lines : line list) : proof_node =
  let arr = Array.of_list lines in
  let n = Array.length arr in

  let rec go pos =
    if pos >= n then
      raise (Ill_formed_replay "replay ends before proof is complete")
    else
      let ((rule_name, arg), rhs) = arr.(pos) in
      let goal = goal_of_rhs rhs in
      let arity = replay_arity rule_name in

      (* Skip phantom entries (FIN, STOP_NORM, NRM) *)
      if arity = -1 then
        go (pos + 1)

      (* _1 rule: start of an equality chain preceding ALL7/XST8.
         Collect the chain (postorder), build it, then build the
         branching quantifier with child1=chain, child2=continuation. *)
      else if is_primed_rule rule_name then begin
        match collect_primed arr n pos with
        | Some (primed_lines, branch_pos) ->
          let child1 = build_postorder primed_lines in
          let ((bname, barg), brhs) = arr.(branch_pos) in
          let bgoal = goal_of_rhs brhs in
          (* Extract FIN result from the line after the branching quant *)
          let fin_pos = branch_pos + 1 in
          let fin_arg =
            if fin_pos < n then
              match snd arr.(fin_pos) with
              | Fin (p, _, _, _) -> Some (Pred p)
              | _ -> barg
            else barg
          in
          let pos2 = skip_fin arr n fin_pos in
          if pos2 >= n then
            raise (Ill_formed_replay
              (Printf.sprintf "%s at end of replay — missing second child"
                 bname))
          else
            let (child2, pos3) = go pos2 in
            (Apply { rule = bname; arg = fin_arg; goal = bgoal;
                     children = [child1; child2] },
             pos3)
        | None ->
          raise (Ill_formed_replay
            (Printf.sprintf "%s without a following ALL7/XST8" rule_name))
      end

      (* Leaf rule (arity 0) *)
      else if arity = 0 then
        (Apply { rule = rule_name; arg; goal; children = [] },
         pos + 1)

      (* Single-child rule (arity 1) *)
      else if arity = 1 then
        let (child, next_pos) = go (pos + 1) in
        (Apply { rule = rule_name; arg; goal; children = [child] },
         next_pos)

      (* Two-child rule (arity 2). ALL7/XST8 are branching quantifiers
         and always arrive here via the primed-chain path above — they
         never appear as a bare entry without a preceding _1 chain. *)
      else begin
        if is_branching_quantifier rule_name then
          raise (Ill_formed_replay
            (Printf.sprintf "%s without a preceding _1 equality chain"
               rule_name));
        let (child1, pos1) = go (pos + 1) in
        let (child2, pos2) = go pos1 in
        (Apply { rule = rule_name; arg; goal;
                 children = [child1; child2] },
         pos2)
      end
  in

  let (tree, final_pos) = go 0 in
  (* Trailing phantoms (FIN/STOP_NORM/NRM after the root proof) carry
     no information; advance past them before deciding whether real
     content was left unconsumed. *)
  let final_pos = skip_phantoms arr n final_pos in
  if final_pos < n then
    Printf.eprintf "warning: %d unconsumed lines in proof tree\n"
      (n - final_pos);
  tree
