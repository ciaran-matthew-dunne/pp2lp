open Syntax_pp

type proof_node =
  | Apply of {
      rule: string;
      arg: arg option;
      goal: prd;
      children: proof_node list;
    }

exception Build of string


let is_base_rule : string -> bool =
  fun str -> not (String.ends_with ~suffix:"_1" str)

(** Collect the replay steps for a result derivation.
    Scans forward from [pos] through _1-suffixed rules
    until a result-consuming base rule is found.
      (i.e., ALL7 or XST8).

    Returns [(ls, k)] where
    - [ls]: the _1 lines forming the equality derivation
    - [k]: position of the ALL7/XST8 that consumes the result
*)
let rec collect_result_lines arr n pos =
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


let build (ls : line list) : proof_node =
  let arr = Array.of_list ls in
  let n = Array.length arr in

  let rec go (k : int) : proof_node * int =
    if k >= n then
      failwith "error in `go`: position index exceeds array length"
    else
      begin match arr.(k) with
      | ((rule, arg), Simple goal) ->
        if is_base_rule rule then
          begin match Rule_db.rule_arity rule with
          | 0 ->
            (Apply { rule; arg; goal; children = [] }, k + 1)
          | 1 ->
          let (ch, k') = go (k + 1) in
            (Apply { rule; arg; goal; children = [ch] }, k')
          | 2 ->
            let (ch1, k1) = go (k+1) in
            let (ch2, k2) = go (k1) in
            (Apply {rule; arg; goal; children = [ch1;ch2]}, k2)
          | j -> Printf.ksprintf failwith
              "error in `go`: rule %s has arity %d" rule j
          end
        else


      | _ -> failwith "unhandled `line` shape"
      end
  in
    fst (go 0)
