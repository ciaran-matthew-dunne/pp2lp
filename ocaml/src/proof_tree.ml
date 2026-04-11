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

(* Re-export from Rule_db for convenience *)
let rule_arity = Rule_db.rule_arity
let has_primed = Rule_db.has_primed

(* --- Rule name predicates --- *)

let is_primed_rule name =
  name = "STOP_1" ||
  (String.length name > 2 &&
   String.sub name (String.length name - 2) 2 = "_1")

let is_base_branching_quantifier name =
  match name with
  | "ALL7" | "ALL7f" | "XST8" | "XST8f" -> true
  | _ -> false

let is_branching_quantifier name =
  match name with
  | "ALL7" | "ALL7f" | "XST8" | "XST8f"
  | "ALL7_1" | "ALL7f_1" | "XST8_1" | "XST8f_1" -> true
  | _ -> false

let is_nrm_step name =
  let len = String.length name in
  len > 3 &&
  String.sub name 0 3 = "NRM" &&
  let c = name.[3] in c >= '0' && c <= '9'

(* Resolve rule name based on context: append _1 in Primed context *)
let resolve_rule name ctx =
  match ctx with
  | Base -> name
  | Primed ->
    if Rule_db.has_primed name then name ^ "_1"
    else name

let goal_of_rhs = function
  | Simple p -> p
  | Fin (p, _, _, _) -> p

(* Arity of a rule as it appears in the replay (with _1 suffix).
   For primed rules, strip _1 and look up the base arity.
   XST8_1 is special: base XST8 has arity 2 but XST8_1 has arity 1
   (the ¬¬-elimination is internalised). *)
let replay_arity name =
  if name = "STOP_1" then 0
  else if name = "XST8_1" || name = "XST8f_1" then 1
  else if is_primed_rule name then
    let base = String.sub name 0 (String.length name - 2) in
    Rule_db.rule_arity base
  else
    Rule_db.rule_arity name

let is_phantom name = replay_arity name = -1

(* --- Helpers used by build --- *)

(* Collect primed prefix lines until a BASE ALL7/XST8 is found.
   Returns Some (collected_lines, branch_pos) or None.
   Non-_1 NRM steps (normalisation bookkeeping) are skipped — they
   compute the FIN result but are not equality-chain proof steps. *)
let rec collect_primed arr n pos =
  if pos >= n then None
  else
    let ((name, _), rhs) = arr.(pos) in
    if is_base_branching_quantifier name then
      Some ([], pos)
    else if is_phantom name then begin
      (* Include FIN lines for result extraction, skip other phantoms *)
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

(* Remove non-_1 NRM steps from collected primed lines.
   Non-suffixed NRM steps (NRM1, NRM3, ...) in the primed chain are
   normalisation bookkeeping that PP uses to compute the FIN result.
   Only _1-suffixed NRM steps (NRM1_1, NRM3_1, ...) are actual proof
   steps in the equality chain. *)
let remove_norm_steps (lines : line list) : line list =
  List.filter (fun ((name, _), _) ->
    not (is_nrm_step name && not (is_primed_rule name))
  ) lines

(* Build a primed subtree from post-order lines (leaf-first).
   Stack-based: leaves push, arity-1 pop 1, arity-2 pop 2. *)
let build_postorder (lines : line list) : proof_node =
  let lines = remove_norm_steps lines in
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
      else if arity = 1 then
        let child = pop () in
        push (Apply { rule = rule_name; arg; goal; ctx = Primed; children = [child] })
      else begin
        let child2 = pop () in
        let child1 = pop () in
        push (Apply { rule = rule_name; arg; goal; ctx = Primed;
                      children = [child1; child2] })
      end
    end
  ) lines;
  pop ()

(* Skip phantom lines (FIN, STOP_NORM, NRM) after a branching point *)
let rec skip_phantoms arr n pos =
  if pos >= n then pos
  else
    let ((name, _), _) = arr.(pos) in
    if is_phantom name then skip_phantoms arr n (pos + 1)
    else pos

(* Skip FIN + trailing phantoms *)
let skip_fin arr n pos =
  if pos >= n then pos
  else
    let ((name, _), _) = arr.(pos) in
    if name = "FIN" then skip_phantoms arr n (pos + 1)
    else pos

(* --- Main tree builder --- *)

let build (lines : line list) : proof_node =
  let arr = Array.of_list lines in
  let n = Array.length arr in

  let rec go pos ctx =
    if pos >= n then begin
      Printf.eprintf "warning: incomplete proof, inserting SORRY\n";
      (Apply { rule = "SORRY"; arg = None;
               goal = Lift (Var "incomplete"); ctx;
               children = [] },
       pos)
    end
    else
      let ((rule_name, arg), rhs) = arr.(pos) in
      let arity = replay_arity rule_name in

      if arity = -1 then
        go (pos + 1) ctx

      (* Primed prefix: _1-suffixed rule in Base context signals a primed
         subtree preceding an ALL7/XST8 branching quantifier. *)
      else if ctx = Base && is_primed_rule rule_name then begin
        match collect_primed arr n pos with
        | Some (primed_lines, branch_pos) ->
          let child1 = build_postorder primed_lines in
          let ((bname, _barg), brhs) = arr.(branch_pos) in
          let bgoal = goal_of_rhs brhs in
          let resolved = resolve_rule bname ctx in
          let fin_pos = branch_pos + 1 in
          let fin_arg =
            if fin_pos < n then
              let ((_, _), fin_rhs) = arr.(fin_pos) in
              match fin_rhs with Fin (p, _, _, _) -> Some (Pred p) | _ -> _barg
            else _barg
          in
          let pos2 = skip_fin arr n fin_pos in
          if pos2 >= n then
            failwith (Printf.sprintf
              "proof_tree: %s at end of replay has no child2 \
               (truncated or malformed replay)" bname)
          else
            let (child2, pos3) = go pos2 Base in
            (Apply { rule = resolved; arg = fin_arg; goal = bgoal; ctx;
                     children = [child1; child2] },
             pos3)
        | None ->
          let goal = goal_of_rhs rhs in
          (Apply { rule = rule_name; arg; goal; ctx = Primed;
                   children = [] },
           pos + 1)
      end

      else if rule_name = "STOP_1" then
        let goal = goal_of_rhs rhs in
        (Apply { rule = "STOP_1"; arg; goal; ctx = Primed; children = [] },
         pos + 1)

      else if arity = 0 then
        let resolved = resolve_rule rule_name ctx in
        let goal = goal_of_rhs rhs in
        (Apply { rule = resolved; arg; goal; ctx; children = [] },
         pos + 1)

      else if arity = 1 then
        let resolved = resolve_rule rule_name ctx in
        let goal = goal_of_rhs rhs in
        let (child, next_pos) = go (pos + 1) ctx in
        (Apply { rule = resolved; arg; goal; ctx; children = [child] },
         next_pos)

      else begin
        let goal = goal_of_rhs rhs in
        if is_branching_quantifier rule_name then begin
          let resolved = resolve_rule rule_name ctx in
          let (child1, pos1) = go (pos + 1) Primed in
          let pos2 = skip_fin arr n pos1 in
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
  in

  let (tree, final_pos) = go 0 Base in
  if final_pos < n then
    Printf.eprintf "warning: %d unconsumed lines in proof tree\n" (n - final_pos);
  tree
