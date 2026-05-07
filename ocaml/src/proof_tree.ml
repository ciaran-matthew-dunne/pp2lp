(* Proof tree built from a trace.

   The trace is right-first DFS postorder of the proof tree (children
   before parents).  Stack-based postorder evaluation rebuilds the
   tree in one pass.  The tree carries no per-node goal — emission
   uses only the rule name, the rule's argument (from `[RULE(arg)]`),
   and the children. *)

open Syntax_pp

type pp_tree =
  | Apply of {
      rule: string;
      arg: arg option;
      children: pp_tree list;
    }

exception Bad_trace of string

let bad fmt = Printf.ksprintf (fun s -> raise (Bad_trace s)) fmt

let build (rules : lhs list) : pp_tree =
  let stack = ref ([] : pp_tree list) in
  let push n = stack := n :: !stack in
  let pop name =
    match !stack with
    | [] -> bad "%s expected a child but stack is empty" name
    | x :: rest -> stack := rest; x
  in
  List.iter (fun ((rule_name, arg) : lhs) ->
    if Rule_db.is_phantom rule_name then ()
    else begin
      match Rule_db.rule_arity rule_name with
      | 0 ->
        push (Apply { rule = rule_name; arg; children = [] })
      | 1 ->
        let c = pop rule_name in
        push (Apply { rule = rule_name; arg; children = [c] })
      | 2 ->
        (* Right-first postorder: top-of-stack is child0 (left), the
           one beneath is child1 (right).  Restore [child0; child1]. *)
        let c0 = pop rule_name in
        let c1 = pop rule_name in
        push (Apply { rule = rule_name; arg; children = [c0; c1] })
      | n ->
        bad "%s: unsupported arity %d" rule_name n
    end
  ) rules;
  match !stack with
  | [root] -> root
  | [] -> bad "trace produced no nodes"
  | xs -> bad "trace left %d nodes on stack (expected 1)" (List.length xs)

let rule_of (Apply { rule; _ }) = rule
let arg_of  (Apply { arg; _ })  = arg
let children_of (Apply { children; _ }) = children

let debug = ref false

let rec pp_tree ?(indent="") ?(last=true) ch node =
  let prefix = if last then "+-- " else "|-- " in
  let child_indent = indent ^ (if last then "    " else "|   ") in
  match node with
  | Apply { rule; arg; children } ->
    let arg_s = match arg with
      | None -> ""
      | Some (Pred p) -> Printf.sprintf " (%s)" (Emit_pp.prd_to_pp p)
      | Some (PipeArg (a, b)) ->
        Printf.sprintf " (%s | %s)"
          (Emit_pp.prd_to_pp (Lift a)) (Emit_pp.prd_to_pp (Lift b))
    in
    Printf.fprintf ch "%s%s%s%s\n" indent prefix rule arg_s;
    let n = List.length children in
    List.iteri (fun i c ->
      pp_tree ~indent:child_indent ~last:(i = n - 1) ch c
    ) children

let debug_tree label node =
  if !debug then begin
    Printf.eprintf "=== %s ===\n" label;
    pp_tree ~indent:"" ~last:true stderr node
  end
