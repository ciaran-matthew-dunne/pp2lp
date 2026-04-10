open Syntax_pp

type ctx = Base | Primed

type proof_node =
  | Apply of {
      rule: string;
      arg: arg option;
      goal: prd;
      ctx: ctx;
      children: proof_node list;
    }

let rule_arity (name : string) : int =
  Rule_db.rule_arity name

let has_primed (name : string) : bool =
  Rule_db.has_primed name

(* Resolve rule name based on context *)
let resolve_rule (name : string) (ctx : ctx) : string =
  match ctx with
  | Base -> name
  | Primed ->
    if has_primed name then name ^ "_1"
    else name

(* Extract goal predicate from an rhs *)
let goal_of_rhs = function
  | Simple p -> p
  | Fin (p, _, _, _) -> p

(* Check if a rule name is a primed (_1 suffixed) rule in the replay *)
let is_primed_rule (name : string) : bool =
  name = "STOP_1" ||
  (String.length name > 2 &&
   String.sub name (String.length name - 2) 2 = "_1")

(* Check if a rule is a BASE ALL7/XST8 branching quantifier (non-primed) *)
let is_base_branching_quantifier (name : string) : bool =
  name = "ALL7" || name = "ALL7f" || name = "XST8" || name = "XST8f"

(* Check if a rule is any ALL7/XST8 branching quantifier (base or primed) *)
let is_branching_quantifier (name : string) : bool =
  match name with
  | "ALL7" | "ALL7f" | "XST8" | "XST8f"
  | "ALL7_1" | "ALL7f_1" | "XST8_1" | "XST8f_1" -> true
  | _ -> false

(* Arity of a rule name as it appears in the replay (with _1 suffix).
   For primed rules, strip the _1 suffix and look up the base arity.
   STOP_1 is always a leaf. *)
let replay_arity (name : string) : int =
  if name = "STOP_1" then 0
  else if is_primed_rule name then
    (* Strip _1 suffix to get base name *)
    let base = String.sub name 0 (String.length name - 2) in
    rule_arity base
  else
    rule_arity name

(* Build proof tree from line list *)
let build (lines : line list) : proof_node =
  let arr = Array.of_list lines in
  let n = Array.length arr in

  (* Collect primed prefix lines until a BASE ALL7/XST8 is found.
     Returns Some (collected_lines_in_replay_order, branch_pos)
     or None if no base branching quantifier is found ahead. *)
  let rec collect_primed pos =
    if pos >= n then
      None
    else
      let ((name, _), rhs) = arr.(pos) in
      if is_base_branching_quantifier name then
        Some ([], pos)
      else if rule_arity name = -1 then begin
        (* Include FIN lines (for result extraction), skip other phantoms *)
        match rhs with
        | Fin _ ->
          (match collect_primed (pos + 1) with
           | Some (rest, bp) -> Some (arr.(pos) :: rest, bp)
           | None -> None)
        | _ -> collect_primed (pos + 1)
      end
      else
        match collect_primed (pos + 1) with
        | Some (rest, branch_pos) ->
          Some (arr.(pos) :: rest, branch_pos)
        | None -> None
  in

  (* Build a primed subtree from a list of lines in post-order
     (leaf-first, as they appear in the replay).
     Uses a stack: leaves push, arity-1 pop 1, arity-2 pop 2. *)
  let build_postorder (lines : line list) : proof_node =
    let stack = ref [] in
    let last_fin = ref None in
    let push node = stack := node :: !stack in
    let pop () =
      match !stack with
      | [] -> failwith "proof_tree: build_postorder: empty stack"
      | x :: rest -> stack := rest; x
    in
    List.iter (fun ((rule_name, arg), rhs) ->
      let goal = goal_of_rhs rhs in
      let arity = replay_arity rule_name in
      if arity = -1 then begin
        (* Track FIN results for branching quantifiers *)
        (match rhs with
         | Fin (p, _, _, _) -> last_fin := Some (Pred p)
         | _ -> ())
      end
      else begin
        (* For ALL7_1/XST8_1, attach the preceding FIN result *)
        let arg =
          if is_branching_quantifier rule_name then
            (match !last_fin with
             | Some _ as f -> last_fin := None; f
             | None -> arg)
          else arg
        in
        if arity = 0 then
          push (Apply { rule = rule_name; arg; goal; ctx = Primed; children = [] })
        else if arity = 1 then begin
          let child = pop () in
          push (Apply { rule = rule_name; arg; goal; ctx = Primed; children = [child] })
        end else begin
          (* arity = 2: in post-order, child1 was pushed first, child2 second *)
          let child2 = pop () in
          let child1 = pop () in
        push (Apply { rule = rule_name; arg; goal; ctx = Primed;
                      children = [child1; child2] })
        end
      end
    ) lines;
    pop ()
  in

  let rec go pos ctx =
    if pos >= n then begin
      (* Replay ended — return a sentinel leaf for incomplete proofs *)
      Printf.eprintf "warning: incomplete proof, inserting SORRY\n";
      (Apply { rule = "SORRY"; arg = None;
               goal = Lift (Var "incomplete"); ctx;
               children = [] },
       pos)
    end
    else
      let ((rule_name, arg), rhs) = arr.(pos) in
      let arity = rule_arity rule_name in

      (* Skip phantom lines *)
      if arity = -1 then
        go (pos + 1) ctx

      (* Primed prefix detection: a _1-suffixed rule in Base context
         signals a primed subtree preceding an ALL7/XST8 rule.
         Collect the prefix, find ALL7/XST8, and build the branching node. *)
      else if ctx = Base && is_primed_rule rule_name then begin
        match collect_primed pos with
        | Some (primed_lines, branch_pos) ->
          (* Build primed subtree from post-order lines *)
          let child1 = build_postorder primed_lines in
          (* Build the ALL7/XST8 branching node *)
          let ((bname, _barg), brhs) = arr.(branch_pos) in
          let bgoal = goal_of_rhs brhs in
          let resolved = resolve_rule bname ctx in
          (* Extract result from FIN line (if present) *)
          let fin_pos = branch_pos + 1 in
          let fin_arg =
            if fin_pos < n then
              let ((_, _), fin_rhs) = arr.(fin_pos) in
              match fin_rhs with Fin (p, _, _, _) -> Some (Pred p) | _ -> _barg
            else _barg
          in
          (* Skip FIN + normalization *)
          let pos2 = skip_fin fin_pos in
          (* Second child: base context (if there are lines remaining) *)
          if pos2 >= n then
            (* ALL7/XST8 is terminal — no child2 *)
            failwith (Printf.sprintf "truncated replay at %s: no child2" bname)
          else
            let (child2, pos3) = go pos2 Base in
            (Apply { rule = resolved; arg = fin_arg; goal = bgoal; ctx;
                     children = [child1; child2] },
             pos3)
        | None ->
          (* No ALL7/XST8 found — treat as regular leaf *)
          let goal = goal_of_rhs rhs in
          (Apply { rule = rule_name; arg; goal; ctx = Primed;
                   children = [] },
           pos + 1)
      end

      (* Handle STOP_1 in Primed context — it's a leaf *)
      else if rule_name = "STOP_1" then
        let goal = goal_of_rhs rhs in
        (Apply { rule = "STOP_1"; arg; goal; ctx = Primed; children = [] },
         pos + 1)

      (* Leaf *)
      else if arity = 0 then
        let resolved = resolve_rule rule_name ctx in
        let goal = goal_of_rhs rhs in
        (Apply { rule = resolved; arg; goal; ctx; children = [] },
         pos + 1)

      (* 1-child rule *)
      else if arity = 1 then
        let resolved = resolve_rule rule_name ctx in
        let goal = goal_of_rhs rhs in
        let (child, next_pos) = go (pos + 1) ctx in
        (Apply { rule = resolved; arg; goal; ctx; children = [child] },
         next_pos)

      (* 2-child branching *)
      else begin
        let goal = goal_of_rhs rhs in

        (* ALL7 and XST8 encountered directly (fallback — normally handled
           via primed prefix detection above) *)
        if is_branching_quantifier rule_name then begin
          let resolved = resolve_rule rule_name ctx in
          let (child1, pos1) = go (pos + 1) Primed in
          let pos2 = skip_fin pos1 in
          let (child2, pos3) = go pos2 Base in
          (Apply { rule = resolved; arg; goal; ctx;
                   children = [child1; child2] },
           pos3)
        end else begin
          let resolved = resolve_rule rule_name ctx in
          let (child1, pos1) = go (pos + 1) ctx in
          let (child2, pos2) = go pos1 ctx in
          (Apply { rule = resolved; arg; goal; ctx;
                   children = [child1; child2] },
           pos2)
        end
      end

  and skip_fin pos =
    if pos >= n then pos
    else
      let ((name, _), _) = arr.(pos) in
      match name with
      | "FIN" -> skip_phantom (pos + 1)
      | _ -> pos

  and skip_phantom pos =
    if pos >= n then pos
    else
      let ((name, _), _) = arr.(pos) in
      match name with
      | "STOP_NORM" | "NRM" -> skip_phantom (pos + 1)
      | "FIN" -> skip_phantom (pos + 1)
      | _ -> pos
  in

  let (tree, final_pos) = go 0 Base in
  if final_pos < n then
    Printf.eprintf "warning: %d unconsumed lines in proof tree\n" (n - final_pos);
  tree
