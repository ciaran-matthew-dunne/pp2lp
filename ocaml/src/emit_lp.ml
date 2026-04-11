open Syntax_pp
open Proof_tree
include Pp_lp
include Free_vars
include Subst
include Hyp_ctx
include Rule_args

(* ---- Primed chain emission (rewrite-based) ---- *)

let rec emit_primed_chain buf ctx pad (node : proof_node) =
  match node with
  | Apply { rule; goal; children; _ } ->
    let base = strip_suffix rule in
    let schema = match Rule_db.result_schema base with
      | Some _ as s -> s | None -> Some 1 in
    Buffer.add_string buf "// ";
    Buffer.add_string buf rule;
    Buffer.add_string buf "\n";
    Buffer.add_string buf pad;
    begin match rule, children with
    (* STOP_1: leaf *)
    | "STOP_1", [] ->
      Buffer.add_string buf "refine STOP_1"

    (* HOAS identity: skip *)
    | _, [child] when is_hoas_identity base ->
      emit_primed_chain buf ctx pad child

    (* Schema 0 — leaf *)
    | _, [] when schema = Some 0 ->
      Printf.eprintf "warning: Schema 0 leaf %s in primed chain\n" base;
      Buffer.add_string buf "admit"

    (* IMP4_1: congruence under ⇒ *)
    | _, [child] when base = "IMP4" ->
      Buffer.add_string buf "refine IMP4_1 _;\n";
      Buffer.add_string buf pad;
      emit_primed_chain buf ctx pad child

    (* IMP5_1: strip known antecedent *)
    | _, [child] when base = "IMP5" ->
      let hyp_prd = match goal with
        | Binary (Imp, p, _) -> p | _ -> Lift (Var "?") in
      begin match find_hyp ctx hyp_prd with
      | Some hname ->
        Buffer.add_string buf "refine IMP5_1 ";
        Buffer.add_string buf hname;
        Buffer.add_string buf " _;\n";
        Buffer.add_string buf pad;
        emit_primed_chain buf ctx pad child
      | None ->
        Buffer.add_string buf "refine IMP4_1 _;\n";
        Buffer.add_string buf pad;
        emit_primed_chain buf ctx pad child
      end

    (* ALL8_1: congruence under ∀ *)
    | _, [child] when base = "ALL8" ->
      Buffer.add_string buf "refine ALL8_1 _;\n";
      Buffer.add_string buf pad;
      let vars = match goal with Bind (_, xs, _) -> xs | _ -> [] in
      Buffer.add_string buf "assume";
      List.iter (fun x -> Buffer.add_char buf ' '; pp_ident buf x) vars;
      Buffer.add_string buf ";\n";
      Buffer.add_string buf pad;
      emit_primed_chain buf ctx pad child

    (* ALL9_1: congruence under hypothesis implication *)
    | _, [child] when base = "ALL9" ->
      Buffer.add_string buf "refine ALL9_1 _;\n";
      Buffer.add_string buf pad;
      emit_primed_chain buf ctx pad child

    (* AND5 — structural: antecedent congruence (keep rewrite approach) *)
    | _, [child] when base = "AND5" ->
      Buffer.add_string buf "rewrite (ante_cong";
      emit_rule_args buf ctx rule node;
      Buffer.add_string buf ");\n";
      Buffer.add_string buf pad;
      emit_primed_chain buf ctx pad child

    (* AR9 — solver equality (keep rewrite approach) *)
    | _, [child] when base = "AR9" ->
      let (e_opt, f_opt) = match goal, node with
        | Binary (Imp, Leq (e, _), _),
          Apply { arg = Some (Pred (Lift f)); _ } -> (Some e, Some f)
        | Binary (Imp, Leq (e, _), _),
          Apply { arg = Some (Pred (Leq (f, _))); _ } -> (Some e, Some f)
        | _ -> (None, None)
      in
      begin match e_opt, f_opt with
      | Some e, Some f ->
        let ar9_id = Printf.sprintf "h_ar9_%d" ctx.counter in
        Buffer.add_string buf "have ";
        Buffer.add_string buf ar9_id;
        Buffer.add_string buf " : \xcf\x80 ("; (* π ( *)
        pp_exp buf e;
        Buffer.add_string buf " = ";
        pp_exp buf f;
        Buffer.add_string buf ") { refine trust };\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "rewrite ";
        Buffer.add_string buf ar9_id;
        Buffer.add_string buf ";\n";
        Buffer.add_string buf pad;
        emit_primed_chain buf ctx pad child
      | _ ->
        Printf.eprintf "warning: AR9 primed chain: could not extract E/F\n";
        Buffer.add_string buf "admit"
      end

    (* OPR1/OPR2 — keep rewrite approach *)
    | _, [child] when base = "OPR1" || base = "OPR2" ->
      Buffer.add_string buf "refine IMP4_1 _;\n";
      Buffer.add_string buf pad;
      let eq_hyp = match goal with
        | Binary (Imp, eq, _) -> eq | _ -> Lift (Var "?") in
      let (hname, ctx') = fresh_hyp ctx eq_hyp in
      Buffer.add_string buf "assume ";
      Buffer.add_string buf hname;
      Buffer.add_string buf ";\n";
      Buffer.add_string buf pad;
      if base = "OPR1" then begin
        Buffer.add_string buf "rewrite ";
        Buffer.add_string buf hname
      end else begin
        Buffer.add_string buf "rewrite left ";
        Buffer.add_string buf hname
      end;
      Buffer.add_string buf ";\n";
      Buffer.add_string buf pad;
      emit_primed_chain buf ctx' pad child

    (* ALL7_1/XST8_1: branching quantifiers in _1 chain *)
    | _, [ca; cb] when base = "ALL7" || base = "XST8" ->
      let is_primed_child c = match c with
        | Apply { rule; _ } -> Proof_tree.is_primed_rule rule
      in
      let (primed_child, base_child) =
        if is_primed_child ca then (ca, cb) else (cb, ca)
      in
      if base = "ALL7" then begin
        let bvars = binding_vars goal in
        let inner_pad = pad ^ "  " in
        (* R is the per-element result. Extract from the per-element
           subtree — the first child of the base_child (NRM continuation)
           contains the inner STOP chain whose result is R. *)
        let rec find_leaf_result n = match n with
          | Apply { rule = "STOP_1"; goal; _ } -> goal
          | Apply { children = [c]; _ } -> find_leaf_result c
          | Apply { children = c :: _; _ } -> find_leaf_result c
          | _ -> compute_result primed_child
        in
        let result_prd = find_leaf_result base_child in
        let all7_1_sym = if List.length bvars >= 2 then "ALL7_1_2" else "ALL7_1" in
        Buffer.add_string buf "refine ";
        Buffer.add_string buf all7_1_sym;
        Buffer.add_string buf " (\xce\xbb"; (* λ *)
        List.iter (fun x -> Buffer.add_char buf ' '; pp_ident buf x) bvars;
        Buffer.add_string buf ", ";
        pp_prd buf result_prd;
        Buffer.add_string buf ") _ _\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "{ assume";
        List.iter (fun x -> Buffer.add_char buf ' '; pp_ident buf x) bvars;
        Buffer.add_string buf ";\n";
        Buffer.add_string buf inner_pad;
        emit_primed_chain buf ctx inner_pad primed_child;
        Buffer.add_string buf " }\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "{ ";
        emit_primed_chain buf ctx inner_pad base_child;
        Buffer.add_string buf " }"
      end else begin
        (* XST8_1: continuation proves ((∀x,¬P x)⇒⊥) = S *)
        Buffer.add_string buf "refine XST8_1 _;\n";
        Buffer.add_string buf pad;
        emit_primed_chain buf ctx pad base_child
      end

    (* Schema 2 — branching _1 rules (with simplification) *)
    | _, [child1; child2] when schema = Some 2 ->
      let r1 = compute_result child1 in
      let r2 = compute_result child2 in
      let raw = Binary (And, r1, r2) in
      let simp = simplify_result raw in
      if raw <> simp then begin
        let tmp = Printf.sprintf "h_s%d" ctx.counter in
        Buffer.add_string buf "have ";
        Buffer.add_string buf tmp;
        Buffer.add_string buf " : \xcf\x80 ("; (* π ( *)
        pp_prd buf goal;
        Buffer.add_string buf " = (";
        pp_prd buf raw;
        Buffer.add_string buf "))\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "{ refine ";
        Buffer.add_string buf (String.uppercase_ascii base);
        Buffer.add_string buf "_1 _ _\n";
        Buffer.add_string buf (pad ^ "  ");
        Buffer.add_string buf "{ ";
        emit_primed_chain buf ctx (pad ^ "    ") child1;
        Buffer.add_string buf " }\n";
        Buffer.add_string buf (pad ^ "  ");
        Buffer.add_string buf "{ ";
        emit_primed_chain buf ctx (pad ^ "    ") child2;
        Buffer.add_string buf " } };\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "refine eq_trans ";
        Buffer.add_string buf tmp;
        Buffer.add_string buf " (";
        if is_false r1 then Buffer.add_string buf "\xe2\x8a\xa5\xe2\x88\xa7 _"
        else if is_false r2 then Buffer.add_string buf "\xe2\x88\xa7\xe2\x8a\xa5 _"
        else if is_true r1 then Buffer.add_string buf "\xe2\x8a\xa4\xe2\x88\xa7 _"
        else if is_true r2 then Buffer.add_string buf "\xe2\x88\xa7\xe2\x8a\xa4 _"
        else Buffer.add_string buf "admit";
        Buffer.add_string buf ")"
      end else begin
        Buffer.add_string buf "refine ";
        Buffer.add_string buf (String.uppercase_ascii base);
        Buffer.add_string buf "_1 _ _\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "{ ";
        emit_primed_chain buf ctx (pad ^ "  ") child1;
        Buffer.add_string buf " }\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "{ ";
        emit_primed_chain buf ctx (pad ^ "  ") child2;
        Buffer.add_string buf " }"
      end

    (* Schema 1 — passthrough _1 rules *)
    | _, [child] ->
      Buffer.add_string buf "refine ";
      Buffer.add_string buf (String.uppercase_ascii base);
      Buffer.add_string buf "_1 _;\n";
      Buffer.add_string buf pad;
      emit_primed_chain buf ctx pad child

    (* Fallback *)
    | _ ->
      Printf.eprintf "warning: unhandled primed node %s with %d children\n"
        rule (List.length children);
      Buffer.add_string buf "admit"
    end

(* ---- Branching quantifier emission (ALL7/XST8) ---- *)

and emit_branching_quant buf thm_hyps ctx indent first_pad pad
    eff_rule _node goal child1 child2 =
  (* Equality-based approach:
     refine ALL7 (λ vars, R) _ _
     { assume vars; _1 equality chain }
     { child2 from replay } *)
  let bvars = binding_vars goal in
  let bvars =
    if (eff_rule = "ALL7" || eff_rule = "XST8")
       && List.length bvars > 1
    then (match bvars with x :: _ -> [x] | [] -> [])
    else bvars
  in
  let is_xst8 = eff_rule = "XST8" || eff_rule = "XST8_2" in
  let all7_sym =
    if is_xst8 then
      (if List.length bvars >= 2 then "XST8_2" else "XST8")
    else
      (if List.length bvars >= 2 then "ALL7_2" else "ALL7") in
  let inner_pad = String.make (indent + 2) ' ' in
  (* Get R from FIN result or compute from chain *)
  let result_prd = extract_fin_result _node child1 in
  (* Emit: refine ALL7 (λ vars, R) _ _ { eq_proof } { child2 } *)
  Buffer.add_string buf first_pad;
  Buffer.add_string buf "refine ";
  Buffer.add_string buf all7_sym;
  Buffer.add_string buf " (\xce\xbb"; (* λ *)
  List.iter (fun x ->
    Buffer.add_char buf ' ';
    pp_ident buf x) bvars;
  Buffer.add_string buf ", ";
  pp_prd buf result_prd;
  Buffer.add_string buf ") _ _\n";
  Buffer.add_string buf pad;
  Buffer.add_string buf "{ assume";
  List.iter (fun x ->
    Buffer.add_char buf ' ';
    pp_ident buf x) bvars;
  Buffer.add_string buf ";\n";
  Buffer.add_string buf inner_pad;
  emit_primed_chain buf ctx inner_pad child1;
  Buffer.add_string buf " }\n";
  Buffer.add_string buf pad;
  Buffer.add_string buf "{ ";
  emit_node buf thm_hyps ctx (indent + 2) ~inline:true child2;
  Buffer.add_string buf " }"

(* ---- Generic two-child emission ---- *)

and emit_two_children buf thm_hyps ctx indent first_pad pad
    eff_rule node child1 child2 =
  Buffer.add_string buf first_pad;
  Buffer.add_string buf "refine ";
  Buffer.add_string buf eff_rule;
  emit_rule_args buf ctx eff_rule node;
  Buffer.add_string buf " _ _\n";
  Buffer.add_string buf pad;
  Buffer.add_string buf "{ ";
  emit_node buf thm_hyps ctx (indent + 2) ~inline:true child1;
  Buffer.add_string buf " }\n";
  Buffer.add_string buf pad;
  Buffer.add_string buf "{ ";
  emit_node buf thm_hyps ctx (indent + 2) ~inline:true child2;
  Buffer.add_string buf " }"

(* ---- Proof node emission ---- *)

and emit_node buf thm_hyps ctx indent ?(inline=false) ?(flat=0)
    (node : proof_node) =
  match node with
  | Apply { rule; goal; children; _ } ->
    let pad = String.make indent ' ' in
    let first_pad = if inline then "" else pad in
    let eff_rule = select_variant rule goal children flat in
    (* Emit rule comment for non-trivial nodes *)
    let emit_comment () =
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "// ";
      Buffer.add_string buf rule;
      Buffer.add_string buf "\n"
    in
    begin match children with
    | [] when rule = "SORRY" ->
      Printf.eprintf "warning: emitting admit for incomplete proof\n";
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "admit"

    | [child] when is_hoas_identity rule ->
      let child_flat = compute_child_flat rule flat in
      emit_node buf thm_hyps ctx indent ~inline ~flat:child_flat child

    | [] ->
      emit_comment ();
      Buffer.add_string buf pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf eff_rule;
      emit_rule_args buf ctx eff_rule node

    | [_child] when Proof_tree.is_branching_quantifier rule ->
      failwith (Printf.sprintf "truncated replay at %s: branching quantifier has no child2" rule)

    | [child] when rule = "NRM1" ->
      emit_comment ();
      let extra = nrm1_extra_count goal in
      Buffer.add_string buf pad;
      if extra > 0 then
        Buffer.add_string buf "refine NRM1_2 _"
      else
        Buffer.add_string buf "refine NRM1 _";
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx indent child

    | [_child] when rule = "INS" ->
      emit_comment ();
      emit_ins buf pad ctx

    | [child] when rule = "OPR1" || rule = "OPR2" ->
      emit_comment ();
      let eq_hyp = match goal with
        | Binary (Imp, eq, _) -> eq
        | _ -> Lift (Var "eq") in
      let (hname, ctx') = fresh_hyp ctx eq_hyp in
      Buffer.add_string buf pad;
      Buffer.add_string buf "assume ";
      Buffer.add_string buf hname;
      if not (is_opr_vacuous rule goal) then begin
        Buffer.add_string buf ";\n";
        Buffer.add_string buf pad;
        if rule = "OPR1" then begin
          Buffer.add_string buf "rewrite ";
          Buffer.add_string buf hname
        end else begin
          Buffer.add_string buf "rewrite left ";
          Buffer.add_string buf hname
        end
      end;
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx' indent child

    | [child] ->
      emit_comment ();
      Buffer.add_string buf pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf eff_rule;
      emit_rule_args buf ctx eff_rule node;
      Buffer.add_string buf " _";
      let ctx' = introduce buf pad ctx rule goal flat in
      let child_flat = compute_child_flat eff_rule flat in
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx' indent ~flat:child_flat child

    | [child1; child2] when Proof_tree.is_branching_quantifier rule ->
      emit_comment ();
      emit_branching_quant buf thm_hyps ctx indent pad pad
        eff_rule node goal child1 child2

    | [child1; child2] ->
      emit_comment ();
      emit_two_children buf thm_hyps ctx indent pad pad
        eff_rule node child1 child2

    | _ ->
      emit_comment ();
      Buffer.add_string buf pad;
      Buffer.add_string buf "admit (* too many children *)"
    end

(* ---- Full .lp file generation ---- *)

let lp_header = "require open pp2lp.B pp2lp.Rules;\n"

let emit_symbol (name : string) (goal : prd) (tree : proof_node) : string =
  let buf = Buffer.create 4096 in
  let thm_hyps = extract_theorem_hyps goal in
  let fv = free_vars_of_prd goal in

  Buffer.add_string buf "opaque symbol ";
  Buffer.add_string buf name;

  let prop_list = SS.elements fv.prop_vars in
  let exp_list = SS.elements fv.exp_vars in
  let all_params = ref [] in
  if prop_list <> [] then begin
    Buffer.add_string buf " (";
    List.iteri (fun i v ->
      if i > 0 then Buffer.add_char buf ' ';
      pp_ident buf v) prop_list;
    Buffer.add_string buf " : Prop)";
    all_params := prop_list
  end;
  if exp_list <> [] then begin
    Buffer.add_string buf " (";
    List.iteri (fun i v ->
      if i > 0 then Buffer.add_char buf ' ';
      pp_ident buf v) exp_list;
    Buffer.add_string buf " : \xcf\x84 \xce\xb9)"; (* τ ι *)
    all_params := !all_params @ exp_list
  end;

  Buffer.add_string buf " :\n  \xcf\x80 ("; (* π *)
  pp_prd_block 4 buf goal;
  Buffer.add_string buf ") \xe2\x89\x94\n"; (* ≔ *)

  Buffer.add_string buf "begin\n";

  if !all_params <> [] then begin
    Buffer.add_string buf "  assume ";
    List.iteri (fun i v ->
      if i > 0 then Buffer.add_char buf ' ';
      pp_ident buf v) !all_params;
    Buffer.add_string buf ";\n"
  end;

  let ctx = empty_ctx in
  emit_node buf thm_hyps ctx 2 tree;
  Buffer.add_char buf '\n';
  Buffer.add_string buf "end;\n";
  Buffer.contents buf

let emit_lp (name : string) (goal : prd) (tree : proof_node) : string =
  lp_header ^ "\n" ^ emit_symbol name goal tree
