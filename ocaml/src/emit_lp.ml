open Syntax_pp
open Proof_tree
include Pp_lp
include Free_vars
include Subst
include Hyp_ctx
include Rule_args

(* ---- INS contradiction resolution ----
   Derives ⊥ from context hypotheses using two strategies:
   1. Simple: find a ¬P + P pair in the most recent entries.
   2. Heart: find a ♡-hyp ∀xs.¬(C₁∧...∧Cₙ) whose conjuncts are in context. *)

let ins_simple_resolve ctx =
  match ctx.entries with
  | (neg_name, Unary (Not, p)) :: _ ->
    begin match find_hyp ctx p with
    | Some pos_name -> Some (neg_name, pos_name)
    | None -> None
    end
  | (neg_name, Binary (Imp, p, _)) :: _ ->
    begin match find_hyp ctx p with
    | Some pos_name -> Some (neg_name, pos_name)
    | None -> None
    end
  | _ -> None

(* Wildcard-aware structural comparison.
   Bound variables from ♡/∀ (containing '$') become wildcards. *)
let rec exp_matches pat hyp =
  match pat, hyp with
  | Var v, _ when String.contains v '$' -> true
  | Var a, Var b -> a = b
  | Nat a, Nat b -> a = b
  | App (f1, a1), App (f2, a2) ->
    f1 = f2 && List.length a1 = List.length a2 &&
    List.for_all2 exp_matches a1 a2
  | AOp (o1, a1, b1), AOp (o2, a2, b2) ->
    o1 = o2 && exp_matches a1 a2 && exp_matches b1 b2
  | Neg e1, Neg e2 -> exp_matches e1 e2
  | SetImage (a1, b1), SetImage (a2, b2)
  | Inter (a1, b1), Inter (a2, b2)
  | Union (a1, b1), Union (a2, b2) ->
    exp_matches a1 a2 && exp_matches b1 b2
  | _ -> false
and prd_matches pat hyp =
  match pat, hyp with
  | Lift e1, Lift e2 -> exp_matches e1 e2
  | Unary (o1, p1), Unary (o2, p2) -> o1 = o2 && prd_matches p1 p2
  | Binary (o1, a1, b1), Binary (o2, a2, b2) ->
    o1 = o2 && prd_matches a1 a2 && prd_matches b1 b2
  | Bind (b1, _, body1), Bind (b2, _, body2) ->
    b1 = b2 && prd_matches body1 body2
  | Mem (es1, e1), Mem (es2, e2) ->
    List.length es1 = List.length es2 &&
    List.for_all2 exp_matches es1 es2 && exp_matches e1 e2
  | Eq (a1, b1), Eq (a2, b2)
  | Leq (a1, b1), Leq (a2, b2) ->
    exp_matches a1 a2 && exp_matches b1 b2
  | _ -> false

let ins_heart_resolve ctx =
  let rec count_bind_vars = function
    | Bind (Forall2, xs, inner) ->
      List.length xs + count_bind_vars inner
    | _ -> 0
  in
  let rec extract_neg_body = function
    | Bind (Forall2, _, inner) -> extract_neg_body inner
    | Unary (Not, body) -> Some body
    | _ -> None
  in
  let rec flatten_conj_leaves = function
    | Binary (And, l, r) -> flatten_conj_leaves l @ flatten_conj_leaves r
    | p -> [p]
  in
  let find_matching_hyps leaves entries =
    let find_match leaf =
      List.find_opt (fun (_, p) ->
        (match leaf with Leq _ -> false | _ -> true) &&
        prd_matches leaf p
      ) entries
    in
    let rec go acc = function
      | [] -> Some (List.rev acc)
      | leaf :: rest ->
        match find_match leaf with
        | Some (name, _) -> go (name :: acc) rest
        | None -> None
    in
    go [] leaves
  in
  let build_term heart n_vars conjs =
    let conj_term = match conjs with
      | [] -> assert false
      | first :: rest ->
        List.fold_left (fun acc c ->
          Printf.sprintf "(\xe2\x88\xa7\xe1\xb5\xa2 %s %s)" acc c (* ∧ᵢ *)
        ) first rest
    in
    let underscores = String.concat "" (List.init n_vars (fun _ -> " _")) in
    Printf.sprintf "%s%s %s" heart underscores conj_term
  in
  let rec scan entries = function
    | [] -> None
    | (name, (Bind (Forall2, _, _) as p)) :: rest ->
      let n_vars = count_bind_vars p in
      begin match extract_neg_body p with
      | Some body ->
        let leaves = flatten_conj_leaves body in
        begin match find_matching_hyps leaves entries with
        | Some conjs when conjs <> [] ->
          Some (build_term name n_vars conjs)
        | _ -> scan entries rest
        end
      | None -> scan entries rest
      end
    | entry :: rest -> scan (entry :: entries) rest
  in
  scan [] ctx.entries

let emit_ins buf first_pad ctx =
  match ins_simple_resolve ctx with
  | Some (neg_name, pos_name) ->
    Buffer.add_string buf first_pad;
    Buffer.add_string buf "refine ";
    Buffer.add_string buf neg_name;
    Buffer.add_char buf ' ';
    Buffer.add_string buf pos_name
  | None ->
    match ins_heart_resolve ctx with
    | Some term ->
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf term
    | None ->
      Printf.eprintf "warning: INS could not resolve contradiction\n";
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "admit"

(* ---- NRM1 compound ♢ emission ----
   Counts extra NRM1 applications needed for compound ♢(x,y,...) bindings
   where extra bound variables are not free in the body. *)

let nrm1_extra_count goal =
  match goal with
  | Binary (Imp, Bind (_, xs, body), _) when List.length xs > 1 ->
    let fv = free_vars_of_prd body in
    let extra = List.tl xs in
    if List.exists (fun v ->
      SS.mem v fv.prop_vars || SS.mem v fv.exp_vars) extra
    then 0 else List.length extra
  | _ -> 0

(* ---- Primed chain emission (rewrite-based) ----
   Walks the primed subtree emitting rewrite calls using equation lemmas
   from Rw.lp. Passthrough steps emit `rewrite lemma_eq;`, branching
   steps use `refine conj_eq _ _ { ... } { ... }`, and structural steps
   use `refine imp_cong/forall_cong _`. *)

(* Map base rule name to its rewrite lemma name in Rw.lp.
   Returns None for rules handled specially (HOAS identity, structural). *)
let rw_lemma_of_rule = function
  (* Conjunction *)
  | "AND1" -> Some "and1_eq"
  | "AND2" -> Some "and2_eq"
  | "AND3" -> Some "and3_eq"
  (* Disjunction *)
  | "OR1" -> Some "or1_eq"
  | "OR2" -> Some "or2_eq"
  | "OR3" -> Some "or3_eq"
  | "OR4" -> Some "or4_eq"
  (* Implication *)
  | "IMP1" -> Some "imp1_eq"
  | "IMP2" -> Some "imp2_eq"
  | "IMP3" -> Some "imp3_eq"
  (* Equivalence *)
  | "EQV1" -> Some "eqv1_eq"
  | "EQV2" -> Some "eqv2_eq"
  | "EQV3" -> Some "eqv3_eq"
  | "EQV4" -> Some "eqv4_eq"
  (* Negation *)
  | "NOT1" -> Some "not1_eq"
  | "NOT2" -> Some "\xc2\xac\xc2\xac\xe2\x82\x91_eq" (* ¬¬ₑ_eq — already in Stdlib *)
  (* Truth/Falsehood — these use Stdlib rewrite rules directly *)
  | "VR3" -> Some "\xe2\x8a\xa4\xe2\x87\x92" (* ⊤⇒ *)
  | "VR2" -> Some "\xc2\xac\xe2\x8a\xa4" (* ¬⊤ *)
  | "FX1" -> Some "\xc2\xac\xe2\x8a\xa5" (* ¬⊥ — then ⊤⇒ *)
  (* Equality *)
  | "EVR2" -> Some "\xc2\xac=_idem" (* ¬=_idem *)
  | "EVR3" -> Some "evr3_eq"
  | "OPR1" -> Some "opr1_eq"
  | "OPR2" -> Some "opr2_eq"
  | "EQC1" -> Some "eqc1_eq"
  | "EQC2" -> Some "eqc2_eq"
  | "EQS1" -> Some "eqs1_eq"
  | "EQS2" -> Some "eqs2_eq"
  (* Existential *)
  | "XST7" -> Some "xst7_eq"
  | _ -> None

(* ---- Res term emission ----
   Emits a Res constructor term for the primed chain.
   The term is used inside: refine ALL7r (λ x, <res_term>) _ *)

(* Compute the result Prop from a primed proof tree node (OCaml-side).
   Mirrors the LP-side `result` rewrite rules. *)
let rec compute_result (node : proof_node) : prd =
  match node with
  | Apply { rule; goal; children; _ } ->
    let base = strip_suffix rule in
    match base, children with
    | "STOP", [] -> goal  (* result = P *)
    | _, [child] when is_hoas_identity base -> compute_result child
    (* Schema 1 passthrough *)
    | ("AND2" | "AND3" | "AND5" | "OR4" | "VR3" | "VR2" | "EVR2"
      | "NOT1" | "NOT2" | "OR1" | "IMP1" | "IMP5" | "FX1"
      | "XST7" | "EVR3" | "OPR1" | "OPR2" | "AR9"), [child] ->
      compute_result child
    (* Schema 2 branching *)
    | ("AND1" | "OR3" | "AND4" | "IMP3" | "OR2" | "IMP2"
      | "EQV1" | "EQV2" | "EQV3" | "EQV4"), [child1; child2] ->
      Binary (And, compute_result child1, compute_result child2)
    (* IMP4: P ⇒ child_result *)
    | "IMP4", [child] ->
      let p = match goal with Binary (Imp, p, _) -> p | _ -> goal in
      Binary (Imp, p, compute_result child)
    (* ALL8: ∀x. child_result *)
    | "ALL8", [child] ->
      let vars = match goal with Bind (_, xs, _) -> xs | _ -> [] in
      Bind (Bang, vars, compute_result child)
    (* ALL9: H ⇒ child_result *)
    | "ALL9", [child] ->
      let h = match goal with Binary (Imp, h, _) -> h | _ -> goal in
      Binary (Imp, h, compute_result child)
    | _ -> goal  (* fallback *)

(* Simplify a result predicate using PP's propositional simplifications. *)
let is_true = function Lift (Var ("VRAI" | "TRUE")) -> true | _ -> false
let is_false = function Lift (Var ("FAUX" | "FALSE")) -> true | _ -> false
let prd_false = Lift (Var "FAUX")
let prd_true = Lift (Var "VRAI")

let rec simplify_result p =
  match p with
  | Binary (And, a, b) ->
    let a = simplify_result a and b = simplify_result b in
    if is_false a || is_false b then prd_false
    else if is_true a then b else if is_true b then a
    else Binary (And, a, b)
  | Binary (Or, a, b) ->
    let a = simplify_result a and b = simplify_result b in
    if is_false a then b else if is_false b then a
    else if is_true a || is_true b then prd_true
    else Binary (Or, a, b)
  | Binary (Imp, a, b) ->
    let a = simplify_result a and b = simplify_result b in
    if is_true a then b else if is_false a then prd_true
    else Binary (Imp, a, b)
  | Unary (Not, a) ->
    let a = simplify_result a in
    if is_true a then prd_false else if is_false a then prd_true
    else (match a with Unary (Not, x) -> x | _ -> Unary (Not, a))
  | Eq (e1, e2) when e1 = e2 -> prd_true
  | _ -> p

(* Extract the FIN result from a node's arg field (set by proof tree builder).
   Falls back to compute_result. *)
let extract_fin_result node fallback_child =
  match node with
  | Apply { arg = Some (Pred p); _ } -> p
  | Apply { children; _ } ->
    (* Check children for FIN results *)
    let rec check = function
      | [] -> compute_result fallback_child
      | (Apply { arg = Some (Pred p); _ }) :: _ -> p
      | _ :: rest -> check rest
    in check children

(* DEAD CODE — kept temporarily for compilation *)
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
