open Syntax_pp
open Proof_tree
open Pp_lp
open Free_vars
open Hyp_ctx

open Rule_args
open Result
open Ins

(* Emitter trace flag. When enabled (via `pp2lp emit -trace`), each
   dispatch decision that diverges from the obvious "emit the rule
   name verbatim" path logs a single line to stderr. Format:

       [emit] FILE: TAG <details>

   where TAG identifies the special case (`ar3-bridged`,
   `nrm20-shape-trust`, `nrm21-23-trust`, `all7-2nd-child-trust`,
   …). Off by default — non-trace output is unchanged. *)
let trace = ref false
let trace_file = ref ""

(* Captured trace events (for `pp2lp emit --json` and `pp2lp debug`).
   When [trace_capture] is non-None, records get appended *and* the
   stderr line is suppressed — the consumer wants structured data. *)
type trace_event = { tag : string; details : string }
let trace_capture : trace_event list ref option ref = ref None
let with_trace_capture f =
  let acc = ref [] in
  let prev = !trace_capture in
  trace_capture := Some acc;
  Fun.protect
    ~finally:(fun () -> trace_capture := prev)
    (fun () ->
      let r = f () in
      (r, List.rev !acc))

let trace_emit (tag : string) (details : string) : unit =
  match !trace_capture with
  | Some acc -> acc := { tag; details } :: !acc
  | None ->
    if !trace then
      Printf.eprintf "[emit] %s: %s%s\n"
        (if !trace_file = "" then "?" else Filename.basename !trace_file)
        tag
        (if details = "" then "" else " " ^ details)

(* ---- AR3 dispatch: AR3 (raw) vs AR3' (bridged) ----
   PP emits `[AR3(SOURCE | RESULT)]` where RESULT is the solver-normalised
   form of `1 - SOURCE`. When `1 - SOURCE` reduces to RESULT definitionally,
   the LP rule AR3 fits as-is. When it doesn't, AR3' takes a bridge proof
   of `(𝟏 - SOURCE) = RESULT` so subsequent rules see a hypothesis typed
   directly as `RESULT ≤ 𝟎`. The bridge composes the small proven lemmas
   in B.lp / Arith.lp (`neg_neg`, `sub_sub`, `ar3_bridge_neg`). *)

(* Emit the bridge proof term — composes lemmas from B.lp / Arith.lp.
   Falls back to `trust` for unknown shapes (rare; keeps surface narrow). *)
let emit_ar3_bridge buf source result =
  match source, result with
  | Neg x, AOp (Add, Nat 1, x') when x = x' ->
    Buffer.add_string buf "ar3_bridge_neg ";
    pp_exp buf x
  | AOp (Sub, Nat 1, x), _ when x = result ->
    Buffer.add_string buf "sub_sub \xf0\x9d\x9f\x8f "; (* 𝟏 *)
    pp_exp buf x
  | _ ->
    Buffer.add_string buf "trust"

(* Emit `refine AR3 (SOURCE)` or `refine AR3' (SOURCE) (RESULT) (BRIDGE)`
   depending on whether `1 - SOURCE` matches RESULT structurally. *)
let emit_ar3_dispatch buf node =
  match node with
  | Apply { arg = Some (PipeArg (source, result)); _ } ->
    let one_minus_source = AOp (Sub, Nat 1, source) in
    if one_minus_source = result then begin
      trace_emit "ar3-direct" "";
      Buffer.add_string buf "refine AR3 (";
      pp_exp buf source;
      Buffer.add_string buf ")"
    end else begin
      let bridge_kind = match source, result with
        | Neg _, _ -> "neg"
        | AOp (Sub, Nat 1, x), _ when x = result -> "sub-sub"
        | _ -> "trust"
      in
      trace_emit "ar3-bridged" ("bridge=" ^ bridge_kind);
      Buffer.add_string buf "refine AR3' (";
      pp_exp buf source;
      Buffer.add_string buf ") (";
      pp_exp buf result;
      Buffer.add_string buf ") (";
      emit_ar3_bridge buf source result;
      Buffer.add_string buf ")"
    end
  | _ ->
    raise (Emit_admit "AR3 missing pipe arg")

(* ---- Primed chain emission (rewrite-based) ---- *)

let rec emit_primed_chain buf ctx pad (node : proof_node) =
  match node with
  | Apply { rule; goal; children; _ } ->
    let base = strip_suffix rule in
    (* Number of tree children of the base rule. The _1 form has the
       same Seq/Res slot count: 0 = leaf, 1 = passthrough, 2 = result
       conjunction (AND1, OR2, IMP2, EQV1-4). Branching quantifiers
       (ALL7, XST8) also have 2, but their _1 form is dispatched
       explicitly above the catch-all. *)
    let base_arity =
      try Rule_db.rule_arity base with Failure _ -> 1 in
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

    (* Leaf base rule (arity 0) reaching the chain — shouldn't happen
       except for STOP_1 (handled above); surface a precise error. *)
    | _, [] when base_arity = 0 ->
      raise (Emit_admit
        (Printf.sprintf "leaf %s with no children in primed chain" base))

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
        raise (Emit_admit "AR9 primed chain: could not extract E/F")
      end

    (* OPR1/OPR2 — primed: rewrite `(x = E ⇒ P x)` to `(x = E ⇒ P E)`
       (OPR1) or `(E = x ⇒ P x)` to `(E = x ⇒ P E)` (OPR2) within the
       chain. The bridge `(x = E ⇒ P x) = (x = E ⇒ P E)` holds
       pointwise: when `x = E` both sides are `P E`; when not, both
       are vacuously `⊤`. Emit `refine OPRn_1 (λ x, body) x _;` and
       recurse on the child proving the substituted form. *)
    | _, [child] when base = "OPR1" || base = "OPR2" ->
      let xy = match goal, base with
        | Binary (Imp, Eq (Var x, _), body), "OPR1" -> Some (x, body)
        | Binary (Imp, Eq (_, Var x), body), "OPR2" -> Some (x, body)
        | _ -> None
      in
      begin match xy with
      | Some (x_var, body) ->
        Buffer.add_string buf "refine ";
        Buffer.add_string buf rule;
        Buffer.add_string buf " (\xce\xbb "; (* λ *)
        pp_ident buf x_var;
        Buffer.add_string buf " : \xcf\x84 \xce\xb9, "; (* τ ι *)
        pp_prd buf body;
        Buffer.add_string buf ") ";
        pp_ident buf x_var;
        Buffer.add_string buf " _;\n";
        Buffer.add_string buf pad;
        emit_primed_chain buf ctx pad child
      | None ->
        raise (Emit_admit
          (Printf.sprintf "%s primed chain: unexpected goal shape" base))
      end

    (* ALL7_1/XST8_1: branching quantifiers inside an outer _1 chain.
       Proof_tree.build guarantees child1 is the _1-chain subtree and
       child2 is the continuation — the order never needs swapping. *)
    | _, [primed_child; base_child] when base = "ALL7" || base = "XST8" ->
      if base = "ALL7" then begin
        let bvars = binding_vars goal in
        let inner_pad = pad ^ "  " in
        (* R is the per-element result from the first antecedent (primed_child) *)
        let result_prd = compute_result primed_child in
        (* Check if R depends on the quantifier variables *)
        let fv = free_vars_of_prd result_prd in
        let r_is_constant = List.for_all (fun v ->
          not (SS.mem v fv.prop_vars || SS.mem v fv.exp_vars)) bvars in
        let n = List.length bvars in
        let all7_1_sym = if n >= 2 then Printf.sprintf "ALL7_1_%d" n else "ALL7_1" in
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
        (* If R doesn't depend on bound vars, ♢ x, R is stuck — need NRM1_1 *)
        if r_is_constant then begin
          Buffer.add_string buf "refine NRM1_1 _;\n";
          Buffer.add_string buf inner_pad
        end;
        emit_primed_chain buf ctx inner_pad base_child;
        Buffer.add_string buf " }"
      end else begin
        (* XST8_1: continuation proves ((∀x,¬P x)⇒⊥) = S *)
        let bvars = binding_vars goal in
        let n = List.length bvars in
        let xst8_1_sym =
          if n >= 2 then Printf.sprintf "XST8_1_%d" n else "XST8_1" in
        Buffer.add_string buf "refine ";
        Buffer.add_string buf xst8_1_sym;
        Buffer.add_string buf " _;\n";
        Buffer.add_string buf pad;
        emit_primed_chain buf ctx pad base_child
      end

    (* Two-child base rules (AND1/AND4/OR2/OR3/IMP2/IMP3/EQV1-4):
       primed form produces a conjunction in the result chain. The raw
       right-associated result propagates up; ALL7_2/XST8_2 accept it
       and child2's body bridges to left-assoc via `rewrite ∧_assoc`. *)
    | _, [child1; child2] when base_arity = 2 ->
      let r1 = compute_result child1 in
      let r2 = compute_result child2 in
      let raw = Binary (And, r1, r2) in
      let simp = simplify_result raw in
      if raw <> simp then begin
        (* One side collapses to ⊤/⊥: derive raw first, then simplify. *)
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
        else raise (Emit_admit "Schema 2 conjunction: no TRUE/FALSE simplification found");
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

    (* Single-child base rules — passthrough _1 form. *)
    | _, [child] ->
      Buffer.add_string buf "refine ";
      Buffer.add_string buf (String.uppercase_ascii base);
      Buffer.add_string buf "_1 _;\n";
      Buffer.add_string buf pad;
      emit_primed_chain buf ctx pad child

    (* Fallback *)
    | _ ->
      raise (Emit_admit (Printf.sprintf "unhandled primed node %s with %d children"
        rule (List.length children)))
    end

(* True iff [node]'s subtree contains a NRM rule whose ALL7-second-child
   continuation can't currently be elaborated by Lambdapi.

   NRM20 is itself proved at the leaf (NRM20_3 / NRM20_4 in Nrm.lp) but
   the surrounding right-assoc → left-assoc bridging that
   [emit_branching_quant] prepends to child2 over-fires for
   OR3_1/AND3_1-rich chains — `compute_result child1` builds a wider
   right-associated tree than the elaborated goal actually has, so the
   prepended `rewrite ∧_assoc` calls have nothing to match.  Until that
   bridging is itself fixed, keeping NRM20 in this set preserves the
   trust-collapse and the suite stays at 0 failures.  The leaf NRM20
   dispatch above remains sound and is the entry point for any future
   change that bypasses the collapse. *)
and subtree_hits_admitted_nrm node =
  match node with
  | Apply { rule; children; _ } ->
    let base = Rule_db.strip_suffix rule in
    if base = "NRM20" || base = "NRM21"
       || base = "NRM22" || base = "NRM23"
    then true
    else List.exists subtree_hits_admitted_nrm children

(* ---- Branching quantifier emission (ALL7/XST8) ---- *)

and emit_branching_quant buf ctx indent pad
    eff_rule goal child1 child2 =
  (* Equality-based approach:
     refine ALL7 (λ vars, R) _ _
     { assume vars; _1 equality chain }
     { child2 from replay } *)
  let bvars = binding_vars goal in
  let n = List.length bvars in
  (* Base (non-_n) rules use only the first var; _n variants use all n *)
  let bvars =
    if (eff_rule = "ALL7" || eff_rule = "XST8") && n > 1
    then (match bvars with x :: _ -> [x] | [] -> [])
    else bvars
  in
  let n = List.length bvars in
  let is_xst8 = String.starts_with ~prefix:"XST8" eff_rule in
  let all7_sym =
    if is_xst8 then
      (if n >= 2 then Printf.sprintf "XST8_%d" n else "XST8")
    else
      (if n >= 2 then Printf.sprintf "ALL7_%d" n else "ALL7") in
  let inner_pad = String.make (indent + 2) ' ' in
  (* R is the right-associated conjunction the _1 chain naturally produces.
     AND4_1 has signature (Q=S1)(P=S2)⇒((P∧Q)=(S1∧S2)), so a nested chain
     concludes at a right-associated result. We pass that shape to ALL7_2;
     child2's PP-recorded tactics expect left-assoc, so we prepend
     `rewrite ∧_assoc` N-2 times at the head of child2's body. *)
  let result_prd = compute_result child1 in
  (* Count right-nested ∧ pairs anywhere in the predicate. Each such pair
     needs exactly one `rewrite ∧_assoc` to become left-assoc. *)
  let rec count_rassoc = function
    | Binary (And, a, (Binary (And, _, _) as b)) ->
      1 + count_rassoc a + count_rassoc b
    | Binary (_, a, b) -> count_rassoc a + count_rassoc b
    | Unary (_, a) -> count_rassoc a
    | Bind (_, _, a) -> count_rassoc a
    | _ -> 0
  in
  let n_assoc_rewrites = count_rassoc result_prd in
  (* Emit: refine ALL7 (λ vars, R) _ _ { eq_proof } { child2 } *)
  Buffer.add_string buf pad;
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
  if subtree_hits_admitted_nrm child2 then begin
    (* HOU short-circuit: when child2 chains NRM rules down to an
       admitted NRM21-23 leaf (or to a NRM20 reached through the
       right-assoc bridging that over-fires for OR3_1/AND3_1-rich
       chains), Lambdapi can't infer the implicit P/Q/S of
       NRM7_2/5_2/13_2 against the goal `(♢x y, R x y)` — the lambda
       inside the quantifier defeats higher-order pattern matching.
       Collapse the whole subtree to one trust. *)
    trace_emit "all7-2nd-child-trust"
      (Printf.sprintf "rule=%s nvars=%d" eff_rule (List.length bvars));
    Buffer.add_string buf "refine trust"
  end
  else begin
    for _ = 1 to n_assoc_rewrites do
      Buffer.add_string buf "rewrite \xe2\x88\xa7_assoc; " (* ∧_assoc *)
    done;
    emit_node buf ctx (indent + 2) ~inline:true child2
  end;
  Buffer.add_string buf " }"

(* ---- Generic two-child emission ---- *)

and emit_two_children buf ctx indent pad
    eff_rule node child1 child2 =
  Buffer.add_string buf pad;
  Buffer.add_string buf "refine ";
  Buffer.add_string buf eff_rule;
  emit_rule_args buf ctx eff_rule node;
  Buffer.add_string buf " _ _\n";
  Buffer.add_string buf pad;
  Buffer.add_string buf "{ ";
  emit_node buf ctx (indent + 2) ~inline:true child1;
  Buffer.add_string buf " }\n";
  Buffer.add_string buf pad;
  Buffer.add_string buf "{ ";
  emit_node buf ctx (indent + 2) ~inline:true child2;
  Buffer.add_string buf " }"

(* ---- Proof node emission ---- *)

and emit_node buf ctx indent ?(inline=false) ?(flat=0)
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
      raise (Emit_admit "incomplete proof (SORRY node)")

    | [child] when is_hoas_identity rule ->
      let child_flat = compute_child_flat rule flat in
      emit_node buf ctx indent ~inline ~flat:child_flat child

    | [] ->
      emit_comment ();
      Buffer.add_string buf pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf eff_rule;
      emit_rule_args buf ctx eff_rule node

    | [_child] when Proof_tree.is_branching_quantifier rule ->
      failwith (Printf.sprintf
        "emit: %s has only 1 child (truncated or malformed replay)" rule)

    | [child] when rule = "NRM1" ->
      emit_comment ();
      let extra = nrm1_extra_count goal in
      Buffer.add_string buf pad;
      if extra > 0 then
        Buffer.add_string buf (Printf.sprintf "refine NRM1_%d _" (extra + 1))
      else
        Buffer.add_string buf "refine NRM1 _";
      Buffer.add_string buf ";\n";
      emit_node buf ctx indent child

    | [_child] when rule = "INS" ->
      emit_comment ();
      emit_ins buf pad ctx

    | [child] when rule = "OPR1" || rule = "OPR2" ->
      emit_comment ();
      Buffer.add_string buf pad;
      let ctx' = emit_opr_step buf pad ctx ~base:rule
        ~skip_rewrite:(is_opr_vacuous rule goal) goal in
      Buffer.add_string buf ";\n";
      emit_node buf ctx' indent child

    (* NRM20: PP produces goals of shape `forall2(x, y) · ¬(((x = E) ∧
       A y) ∧ B y) ⇒ Q` (3-conjunct, left-assoc, equality first) or
       `forall2(x, y) · ¬((((x = E) ∧ A y) ∧ B y) ∧ C y) ⇒ Q`
       (4-conjunct). The spec's `P ∧ x = E` is matched up to AC; PP
       always emits the equality leftmost and the body x-free. We
       discharge with NRM20_3 / NRM20_4 in Nrm.lp, which match the
       left-assoc shape exactly and let HOU infer A/B(/C). *)
    | [child] when rule = "NRM20" ->
      let nconj = match goal with
        | Binary (Imp, Bind (Forall2, [x; _y], Unary (Not, body)), _) ->
          let conjs = flatten_conj body in
          (match conjs with
           | Eq (Var x', _) :: rest when x' = x -> Some (List.length rest + 1)
           | _ -> None)
        | _ -> None
      in
      begin match nconj with
      | Some n when n = 3 || n = 4 ->
        emit_comment ();
        Buffer.add_string buf pad;
        Buffer.add_string buf (Printf.sprintf "refine NRM20_%d _;\n" n);
        Buffer.add_string buf pad;
        emit_node buf ctx indent child
      | _ ->
        trace_emit "nrm20-shape-trust" rule;
        emit_comment ();
        Buffer.add_string buf pad;
        Buffer.add_string buf "refine trust"
      end

    (* NRM21-23 not exercised by the corpus; keep trust path until a
       concrete shape demands a sound encoding. *)
    | [_child] when rule = "NRM21" || rule = "NRM22" || rule = "NRM23" ->
      trace_emit "nrm21-23-trust" rule;
      emit_comment ();
      Buffer.add_string buf pad;
      Buffer.add_string buf "refine trust"

    | [child] when rule = "AR3" ->
      emit_comment ();
      Buffer.add_string buf pad;
      emit_ar3_dispatch buf node;
      Buffer.add_string buf " _";
      let ctx' = introduce buf pad ctx rule goal flat in
      let child_flat = compute_child_flat eff_rule flat in
      Buffer.add_string buf ";\n";
      emit_node buf ctx' indent ~flat:child_flat child

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
      emit_node buf ctx' indent ~flat:child_flat child

    | [child1; child2] when Proof_tree.is_branching_quantifier rule ->
      emit_comment ();
      emit_branching_quant buf ctx indent pad
        eff_rule goal child1 child2

    | [child1; child2] ->
      emit_comment ();
      emit_two_children buf ctx indent pad
        eff_rule node child1 child2

    | _ ->
      emit_comment ();
      Buffer.add_string buf pad;
      raise (Emit_admit (Printf.sprintf "%s: too many children (%d)"
        rule (List.length children)))
    end

(* ---- Full .lp file generation ---- *)

let lp_header = "require open pp2lp.B pp2lp.Rules;\n"

let emit_symbol (name : string) (goal : prd) (tree : proof_node) : string =
  let buf = Buffer.create 4096 in
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
  emit_node buf ctx 2 tree;
  Buffer.add_char buf '\n';
  Buffer.add_string buf "end;\n";
  Buffer.contents buf

let emit_lp (name : string) (goal : prd) (tree : proof_node) : string =
  lp_header ^ "\n" ^ emit_symbol name goal tree
