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

(* Rule arity: how many sub-goals does this rule consume? *)
(* 0 = leaf, 1 = one child, 2 = two children (branching) *)
(* -1 = skip this line entirely (phantom/no-op) *)

let rule_arity (name : string) : int =
  match name with
  (* Leaves (0 children) *)
  | "AXM1" | "AXM2" | "AXM3" | "AXM4" | "AXM5" | "AXM6" | "AXM7"
  | "AXM8" | "AXM9"
  | "NRM19"
  | "VR1" | "VR4" | "FX2" | "FX3"
  | "EVR1" | "EVR4" | "EVR11"
  | "ECTR1" | "ECTR2" | "ECTR3" | "ECTR4" | "ECTR5" | "ECTR6"
  | "AR2" | "AR4" | "AR11"
  | "BOOL51" | "BOOL52" -> 0

  (* 2 children (branching) *)
  | "AND1" | "AND4"
  | "OR2" | "OR3"
  | "IMP2" | "IMP3"
  | "EQV1" | "EQV2" | "EQV3" | "EQV4"
  | "ALL7" | "ALL7f"
  | "XST8" | "XST8f" -> 2

  (* Skip lines *)
  | "FIN" | "STOP_NORM" | "NRM" -> -1

  (* No-op: AR10 is a solver confirmation, skip it *)
  | "AR10" -> -1

  (* Everything else: 1 child *)
  | _ -> 1

(* Whether a rule has a primed (_1) variant *)
let has_primed name =
  match name with
  | "AND1" | "AND2" | "AND3" | "AND4" | "AND5"
  | "OR1" | "OR2" | "OR3" | "OR4"
  | "IMP1" | "IMP2" | "IMP3" | "IMP4" | "IMP5"
  | "EQV1" | "EQV2" | "EQV3" | "EQV4"
  | "NOT1" | "NOT2"
  | "AXM1" | "AXM2" | "AXM3" | "AXM4" | "AXM5" | "AXM6" | "AXM7"
  | "AXM8" | "AXM9"
  | "ALL1" | "ALL2" | "ALL3" | "ALL4" | "ALL5" | "ALL5f"
  | "ALL6" | "ALL7" | "ALL7f" | "ALL8" | "ALL8f" | "ALL9"
  | "XST1" | "XST2" | "XST3" | "XST4" | "XST5" | "XST51"
  | "XST6" | "XST61" | "XST7" | "XST7f" | "XST8" | "XST8f"
  | "VR1" | "VR2" | "VR3" | "VR4" | "FX1" | "FX2" | "FX3"
  | "STOP"
  | "EVR1" | "EVR2" | "EVR3" | "EVR4" | "EVR11"
  | "EAXM1" | "EAXM2" | "EAXM31" | "EAXM32"
  | "EIMP51" | "EIMP52"
  | "EAXM91" | "EAXM92"
  | "ECTR1" | "ECTR2" | "ECTR3" | "ECTR4" | "ECTR5" | "ECTR6"
  | "NRM1" | "NRM2" | "NRM3" | "NRM4" | "NRM5" | "NRM6" | "NRM7"
  | "NRM8" | "NRM8c" | "NRM8f" | "NRM9" | "NRM9f"
  | "NRM10" | "NRM11" | "NRM12"
  | "NRM13" | "NRM14" | "NRM15" | "NRM16" | "NRM17" | "NRM18"
  | "NRM19" | "NRM20" | "NRM21" | "NRM22" | "NRM23" | "NRM24"
  | "NRM25" | "NRM26" | "NRM27" | "NRM28" | "NRM29" | "NRM30"
  | "AR1" | "AR2" | "AR3" | "AR3_F" | "AR4" | "AR5" | "AR6" | "AR7" | "AR8"
  | "AR9" | "AR10" | "AR11" | "AR12" | "AR13"
  | "AR5_2" | "AR6_2" | "AR7_2" | "AR8_2"
  | "OPR1" | "OPR2"
  | "EQC1" | "EQC2" | "EQS1" | "EQS2"
  | "BOOL11" | "BOOL12" | "BOOL21" | "BOOL22"
  | "BOOL31" | "BOOL32" | "BOOL41" | "BOOL42"
  | "BOOL51" | "BOOL52" -> true
  | _ -> false

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
      let ((name, _), _) = arr.(pos) in
      if is_base_branching_quantifier name then
        Some ([], pos)
      else if rule_arity name = -1 then
        collect_primed (pos + 1)
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
    let push node = stack := node :: !stack in
    let pop () =
      match !stack with
      | [] -> failwith "proof_tree: build_postorder: empty stack"
      | x :: rest -> stack := rest; x
    in
    List.iter (fun ((rule_name, arg), rhs) ->
      let goal = goal_of_rhs rhs in
      let arity = replay_arity rule_name in
      if arity = -1 then
        () (* skip phantom lines *)
      else if arity = 0 then
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
    ) lines;
    pop ()
  in

  let rec go pos ctx =
    if pos >= n then
      (* Replay ended — return a sentinel leaf for incomplete proofs *)
      (Apply { rule = "SORRY"; arg = None;
               goal = Lift (Var "incomplete"); ctx;
               children = [] },
       pos)
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
          let ((bname, barg), brhs) = arr.(branch_pos) in
          let bgoal = goal_of_rhs brhs in
          let resolved = resolve_rule bname ctx in
          (* Skip FIN + normalization *)
          let pos2 = skip_fin (branch_pos + 1) in
          (* Second child: base context (if there are lines remaining) *)
          if pos2 >= n then
            (* ALL7/XST8 is terminal — no child2 *)
            (Apply { rule = resolved; arg = barg; goal = bgoal; ctx;
                     children = [child1] },
             pos2)
          else
            let (child2, pos3) = go pos2 Base in
            (Apply { rule = resolved; arg = barg; goal = bgoal; ctx;
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

  let (tree, _final_pos) = go 0 Base in
  tree
