open Syntax_pp
open Proof_tree
open Pp_lp
open Free_vars
open Subst
open Hyp_ctx

(* ---- Variant selection ----
   Selects the effective LP rule name based on goal shape and context.
   Handles _2 variants, NRM8+NRM13 fusion, and HOAS identity skip. *)

let is_opr_vacuous rule goal =
  (rule = "OPR1" || rule = "OPR2") &&
  match goal with
  | Binary (Imp, Eq (Var x, _), body) when rule = "OPR1" ->
    let fv = free_vars_of_prd body in
    not (SS.mem x fv.exp_vars || SS.mem x fv.prop_vars)
  | Binary (Imp, Eq (_, Var x), body) when rule = "OPR2" ->
    let fv = free_vars_of_prd body in
    not (SS.mem x fv.exp_vars || SS.mem x fv.prop_vars)
  | _ -> false

let is_hoas_identity = function
  | "ALL1" | "ALL2" | "ALL3" | "ALL4" | "ALL6"
  | "XST1" | "XST2" | "XST3" | "XST4"
  | "AR3_F"
  | "NRM8" -> true
  | _ -> false

(* Extract the binder variables from a goal of shape
   [ Bind | ¬Bind | Bind ⇒ _ | ¬Bind ⇒ _ ]. *)
let binding_vars = function
  | Binary (Imp, Bind (_, xs, _), _)
  | Binary (Imp, Unary (Not, Bind (_, xs, _)), _)
  | Bind (_, xs, _)
  | Unary (Not, Bind (_, xs, _)) -> xs
  | _ -> []

let goal_binding_count goal = List.length (binding_vars goal)

let check_compound_limit rule n =
  if n > 3 then
    raise (Proof_tree.Emit_admit
      (Printf.sprintf "%s: compound quantifier binds %d variables (max 3)" rule n))

let select_variant rule goal children flat =
  let n = goal_binding_count goal in
  match rule, children with
  | ("ALL7" | "ALL7_1"), _ when n >= 2 && flat = 0 ->
    check_compound_limit rule n;
    if rule = "ALL7_1" then Printf.sprintf "ALL7_1_%d" n
    else Printf.sprintf "ALL7_%d" n
  | "XST8", _ when n >= 2 && flat = 0 ->
    check_compound_limit rule n;
    Printf.sprintf "XST8_%d" n
  | ("ALL5" | "XST5" | "XST6" | "XST7"
    | "NRM1" | "NRM3" | "NRM5" | "NRM7" | "NRM12" | "NRM13"
    | "NRM14" | "NRM15" | "NRM19"), _
    when n >= 2 ->
    check_compound_limit rule n;
    Printf.sprintf "%s_%d" rule n
  | _ -> rule

(* ---- Suffix handling ---- *)

(* Re-exported from Rule_db so callers in this file (and emit_lp.ml via
   Rule_args.strip_suffix) don't need to know where they live. *)
let strip_suffix = Rule_db.strip_suffix
let is_primed = Rule_db.is_primed
let nary_count = Rule_db.nary_count

(* ---- Child flat propagation ---- *)

let compute_child_flat rule flat =
  let base = strip_suffix rule in
  match base with
  | "ALL5" | "XST5" | "XST7" ->
    if rule = base then flat + 1 else 0  (* _n variants reset flat *)
  | _ when is_hoas_identity rule -> flat
  | _ -> 0

(* ---- Hypothesis/variable introduction ---- *)

let introduces_antecedent = function
  | "IMP4" | "IMP4_1" | "AR12" | "AR12_1" | "ALL9" -> true
  | _ -> false

let introduce buf pad ctx rule goal flat =
  let ctx =
    if introduces_antecedent rule then
      match goal with
      | Binary (Imp, p, _) ->
        let (name, ctx') = fresh_hyp ctx p in
        Buffer.add_string buf ";\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "assume ";
        Buffer.add_string buf name;
        ctx'
      | _ -> ctx
    else ctx
  in
  if rule = "ALL8" || rule = "ALL8_1" then begin
    match goal with
    | Bind (_, xs, _) ->
      let vars = if flat > 0 && List.length xs > flat
        then List.filteri (fun i _ -> i < List.length xs - flat) xs
        else xs
      in
      Buffer.add_string buf ";\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "assume";
      List.iter (fun x ->
        Buffer.add_char buf ' ';
        pp_ident buf x) vars
    | _ -> ()
  end;
  ctx

(* ---- Dynamic argument emitters ---- *)

let find_axm_hyp ctx rule goal =
  match rule, goal with
  | "AXM1", Binary (Imp, p, _) -> find_hyp ctx (Unary (Not, p))
  | "AXM2", Binary (Imp, Unary (Not, p), _) -> find_hyp ctx p
  | "AXM3", p -> find_hyp ctx p
  | "AXM4", Binary (Imp, _, r) -> find_hyp ctx r
  | "AXM4", p -> find_hyp ctx p
  | "AXM5", Binary (Imp, _, Binary (Imp, q, _)) ->
    find_hyp ctx (Unary (Not, q))
  | "AXM6", Binary (Imp, _, Binary (Imp, Unary (Not, q), _)) ->
    find_hyp ctx q
  | "EAXM1", Binary (Imp, Eq (e, f), _) ->
    find_hyp ctx (Unary (Not, Eq (f, e)))
  | "EAXM2", Binary (Imp, Unary (Not, Eq (e, f)), _) ->
    find_hyp ctx (Eq (f, e))
  | _ -> None

let emit_axm8_args buf goal =
  let conjs = match goal with
    | Binary (Imp, ante, _) -> flatten_conj ante | _ -> [] in
  let n = List.length conjs in
  let r = match goal with Binary (Imp, _, r) -> Some r | _ -> None in
  match r with
  | Some r ->
    let rec find idx = function
      | [] -> None | elt :: rest ->
        if elt = r then Some idx else find (idx + 1) rest
    in
    begin match find 0 conjs with
    | Some i ->
      Buffer.add_string buf " (\xce\xbb h, "; (* λ h, *)
      emit_extract buf "h" n i;
      Buffer.add_char buf ')'
    | None -> Buffer.add_string buf " _"
    end
  | None -> Buffer.add_string buf " _"

let emit_axm9_args buf ctx =
  let rec has_true_and = function
    | Unary (Not, Binary (And, Lift (Var ("VRAI"|"TRUE")), _)) -> true
    | Bind (_, _, body) -> has_true_and body
    | _ -> false
  in
  let rec count_bind_depth = function
    | Bind (_, xs, body) -> List.length xs + count_bind_depth body
    | _ -> 0
  in
  let rec search = function
    | [] -> None
    | (name, (Bind (_, _, body) as p)) :: rest ->
      if has_true_and body then Some (name, count_bind_depth p)
      else search rest
    | _ :: rest -> search rest
  in
  match search ctx.entries with
  | Some (name, nvars) when nvars >= 2 ->
    Buffer.add_string buf (Printf.sprintf "_%d" nvars);
    for _ = 1 to nvars do Buffer.add_string buf " _" done;
    Buffer.add_char buf ' ';
    Buffer.add_string buf name
  | Some (name, _) ->
    Buffer.add_string buf " _ ";
    Buffer.add_string buf name
  | None ->
    Buffer.add_string buf " _ _"

let emit_and5_args buf goal node ~primed =
  let children = match node with Apply { children; _ } -> children in
  let child_goal = match children with
    | [Apply { goal; _ }] -> Some goal | _ -> None in
  let conjs = match goal with
    | Binary (Imp, ante, _) -> flatten_conj ante | _ -> [] in
  let n = List.length conjs in
  let find_and5_indices child_goal =
    let parent_list = conjs in
    let child_list = match child_goal with
      | Binary (Imp, ante, _) -> flatten_conj ante | _ -> [] in
    let rec find_j pi ci =
      if pi >= n then None
      else
        let p_elt = List.nth parent_list pi in
        if ci < List.length child_list && p_elt = List.nth child_list ci then
          find_j (pi + 1) (ci + 1)
        else Some pi
    in
    match find_j 0 0 with
    | None -> None
    | Some j ->
      match List.nth parent_list j with
      | Binary (Imp, a, _) ->
        let rec find_i idx = function
          | [] -> None | elt :: rest ->
            if elt = a && idx <> j then Some idx
            else find_i (idx + 1) rest
        in
        begin match find_i 0 parent_list with
        | Some i -> Some (i, j) | None -> None
        end
      | _ -> None
  in
  match child_goal with
  | Some cg ->
    begin match find_and5_indices cg with
    | Some (i, j) ->
      Buffer.add_string buf " (\xce\xbb h, "; (* λ h, *)
      emit_and5_fwd buf "h" n i j;
      Buffer.add_char buf ')';
      if primed then begin
        Buffer.add_string buf " (\xce\xbb h, "; (* λ h, *)
        emit_and5_bwd buf "h" n j;
        Buffer.add_char buf ')'
      end
    | None ->
      Buffer.add_string buf (if primed then " _ _" else " _")
    end
  | None ->
    Buffer.add_string buf (if primed then " _ _" else " _")

let rec right_assoc_conj = function
  | Binary (And, Binary (And, a, b), c) ->
    right_assoc_conj (Binary (And, a, Binary (And, b, c)))
  | p -> p

let emit_quant_r_args buf rule node =
  match node with
  | Apply { children; _ } ->
    let extract_r child_goal =
      match child_goal with
      | Binary (Imp, Bind ((Bang|Forall|Forall2), xs, r_body), _) ->
        if nary_count rule >= 2 then
          Some (xs, [], right_assoc_conj r_body)
        else
          let lambda_vars = (match xs with x :: _ -> [x] | [] -> []) in
          let inner_vars = (match xs with _ :: rest -> rest | [] -> []) in
          Some (lambda_vars, inner_vars, right_assoc_conj r_body)
      | _ -> None
    in
    let r_opt = match children with
      | [_; Apply { goal; _ }] -> extract_r goal
      | [Apply { goal; _ }] -> extract_r goal
      | _ -> None
    in
    begin match r_opt with
    | Some (lambda_vars, inner_vars, r_body) ->
      Buffer.add_string buf " (\xce\xbb"; (* (λ *)
      List.iter (fun x ->
        Buffer.add_char buf ' ';
        pp_ident buf x) lambda_vars;
      Buffer.add_string buf ", ";
      if inner_vars <> [] then begin
        Buffer.add_string buf "(`\xe2\x88\x80 "; (* (`∀ *)
        List.iter (fun x ->
          pp_ident buf x;
          Buffer.add_string buf " : \xcf\x84 \xce\xb9, "
        ) inner_vars;
        pp_prd buf r_body;
        Buffer.add_char buf ')'
      end else
        pp_prd buf r_body;
      Buffer.add_char buf ')'
    | None -> ()
    end

let emit_opr_args buf (node : proof_node) =
  let child_body = match node with
    | Apply { children = [Apply { goal = Binary (Imp, _, body); _ }]; _ } -> Some body
    | _ -> None
  in
  match child_body with
  | Some body ->
    Buffer.add_string buf " (";
    pp_prd buf body;
    Buffer.add_char buf ')'
  | None ->
    Buffer.add_string buf " _"

(* Shared [assume h; rewrite [left] h] fragment for OPR1/OPR2.
   - [base] is "OPR1" (rewrite) or "OPR2" (rewrite left).
   - [skip_rewrite] is set by the caller when the rewrite is vacuous
     (base case only; primed chain always rewrites).
   Emits into [buf] at the current position, assuming the caller has
   already written any leading padding. Returns the extended context. *)
let emit_opr_step buf pad ctx ~base ~skip_rewrite goal =
  let eq_hyp = match goal with
    | Binary (Imp, eq, _) -> eq
    | _ -> Lift (Var "eq") in
  let (hname, ctx') = fresh_hyp ctx eq_hyp in
  Buffer.add_string buf "assume ";
  Buffer.add_string buf hname;
  if not skip_rewrite then begin
    Buffer.add_string buf ";\n";
    Buffer.add_string buf pad;
    Buffer.add_string buf
      (if base = "OPR1" then "rewrite " else "rewrite left ");
    Buffer.add_string buf hname
  end;
  ctx'

let emit_ar3_args buf node =
  match node with
  | Apply { arg = Some (PipeArg (_a_expr, result_expr)); _ } ->
    Buffer.add_string buf " (";
    pp_exp buf result_expr;
    Buffer.add_string buf ") trust"
  | _ ->
    raise (Emit_admit "AR3 missing pipe arg")

let emit_ar4_args buf ctx _goal =
  let found = List.find_opt (fun (_name, p) ->
    match p with Leq (_, Nat 0) -> true | _ -> false
  ) ctx.entries in
  match found with
  | Some (name, Leq (f_expr, _)) ->
    Buffer.add_string buf " (";
    pp_exp buf f_expr;
    Buffer.add_string buf ") ";
    Buffer.add_string buf name;
    Buffer.add_string buf " \xe2\x8a\xa4\xe1\xb5\xa2" (* ⊤ᵢ *)
  | _ ->
    raise (Emit_admit "AR4 could not find F ≤ 0 hypothesis")

let emit_ar56_args buf =
  Buffer.add_string buf " trust"

let emit_ar78_args buf base (node : proof_node) =
  match base with
  | "AR8" ->
    let a_exp = match node with
      | Apply { children = [Apply { goal = Binary (Imp, Eq (_, e2), _); _ }]; _ } ->
        Some e2
      | _ -> None
    in
    begin match a_exp with
    | Some e ->
      Buffer.add_string buf " (";
      pp_exp buf e;
      Buffer.add_string buf ") trust trust"
    | None ->
      raise (Emit_admit "AR8 could not extract a from child equality")
    end
  | _ ->
    Buffer.add_string buf " \xf0\x9d\x9f\x8e trust trust" (* 𝟎 *)

let emit_nrm19_args buf ctx goal =
  let nrm19_body = match goal with
    | Binary (Imp, Bind (Forall2, xs, Unary (Not, Binary (And, _, body))), _) ->
      Some (xs, body)
    | _ -> None
  in
  match nrm19_body with
  | Some (bvars, body) ->
    let rec search = function
      | [] -> None
      | (name, hyp_prd) :: rest ->
        let try_match body hyp_prd = match body, hyp_prd with
          | Lift (App (f1, args1)), Lift (App (f2, args2))
            when f1 = f2 && List.length args1 = List.length args2 ->
            let pairs = List.combine args1 args2 in
            let mapping = List.filter_map (fun (a, h) ->
              match a with
              | Var v when List.mem v bvars -> Some (v, h)
              | _ -> None) pairs in
            if List.length mapping = List.length bvars then
              let body' = List.fold_left (fun acc (v, e) ->
                subst_prd v (match e with Var s -> s | _ -> "_") acc
              ) body mapping in
              if body' = hyp_prd then Some (List.map snd mapping) else None
            else None
          | Mem (es1, e1), Mem (es2, e2)
            when List.length es1 = List.length es2 ->
            let pairs = List.combine (es1 @ [e1]) (es2 @ [e2]) in
            let mapping = List.filter_map (fun (a, h) ->
              match a with
              | Var v when List.mem v bvars -> Some (v, h)
              | _ -> None) pairs in
            if List.length mapping = List.length bvars then
              let body' = List.fold_left (fun acc (v, e) ->
                subst_prd v (match e with Var s -> s | _ -> "_") acc
              ) body mapping in
              if body' = hyp_prd then Some (List.map snd mapping) else None
            else None
          | _ -> None
        in
        begin match try_match body hyp_prd with
        | Some witness_exps -> Some (name, witness_exps)
        | None -> search rest
        end
    in
    begin match search ctx.entries with
    | Some (hyp_name, witness_exps) ->
      List.iter (fun e ->
        Buffer.add_char buf ' ';
        pp_exp buf e) witness_exps;
      Buffer.add_char buf ' ';
      Buffer.add_string buf hyp_name
    | None ->
      List.iter (fun _ -> Buffer.add_string buf " _") bvars;
      Buffer.add_string buf " _"
    end
  | None ->
    Buffer.add_string buf " _ _"

(* ---- Unified rule argument emission ---- *)

let emit_rule_args buf ctx eff_rule (node : proof_node) =
  match node with
  | Apply { goal; arg; _ } ->
    let base = strip_suffix eff_rule in
    let primed = is_primed eff_rule in
    let ea = Rule_db.emit_args base in
    match ea with
    | Some "dynamic:axm8" -> emit_axm8_args buf goal
    | Some "dynamic:and5" -> emit_and5_args buf goal node ~primed
    | Some "dynamic:ar9" ->
      begin match arg with
      | Some (Pred p) ->
        Buffer.add_string buf " (";
        pp_prd buf p;
        Buffer.add_string buf ") trust"
      | _ ->
        raise (Emit_admit "AR9 missing solver arg")
      end
    | Some "dynamic:opr1" -> emit_opr_args buf node
    | Some "dynamic:opr2" -> emit_opr_args buf node
    | _ when primed ->
      begin match ea with
      | Some args when not (String.length args > 8 && String.sub args 0 8 = "dynamic:") ->
        Buffer.add_char buf ' ';
        Buffer.add_string buf args
      | _ -> ()
      end
    | Some "dynamic:hyp" ->
      begin match find_axm_hyp ctx base goal with
      | Some name -> Buffer.add_char buf ' '; Buffer.add_string buf name
      | None -> Buffer.add_string buf " _"
      end
    | Some "dynamic:axm9" -> emit_axm9_args buf ctx
    | Some "dynamic:all7" | Some "dynamic:xst8" ->
      emit_quant_r_args buf eff_rule node
    | Some "dynamic:ar3" -> emit_ar3_args buf node
    | Some "dynamic:ar4" -> emit_ar4_args buf ctx goal
    | Some "dynamic:ar56" -> emit_ar56_args buf
    | Some "dynamic:ar78" -> emit_ar78_args buf base node
    | Some "dynamic:nrm19" -> emit_nrm19_args buf ctx goal
    | Some args ->
      Buffer.add_char buf ' ';
      Buffer.add_string buf args
    | None -> ()

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
   Variables in the wildcards set, or containing '$', match anything. *)
let rec exp_matches wildcards pat hyp =
  match pat, hyp with
  | Var v, _ when SS.mem v wildcards || String.contains v '$' -> true
  | Var a, Var b -> a = b
  | Nat a, Nat b -> a = b
  | App (f1, a1), App (f2, a2) ->
    f1 = f2 && List.length a1 = List.length a2 &&
    List.for_all2 (exp_matches wildcards) a1 a2
  | AOp (o1, a1, b1), AOp (o2, a2, b2) ->
    o1 = o2 && exp_matches wildcards a1 a2 && exp_matches wildcards b1 b2
  | Neg e1, Neg e2 -> exp_matches wildcards e1 e2
  | SetImage (a1, b1), SetImage (a2, b2)
  | Inter (a1, b1), Inter (a2, b2)
  | Union (a1, b1), Union (a2, b2) ->
    exp_matches wildcards a1 a2 && exp_matches wildcards b1 b2
  | _ -> false
and prd_matches wildcards pat hyp =
  match pat, hyp with
  | Lift e1, Lift e2 -> exp_matches wildcards e1 e2
  | Unary (o1, p1), Unary (o2, p2) -> o1 = o2 && prd_matches wildcards p1 p2
  | Binary (o1, a1, b1), Binary (o2, a2, b2) ->
    o1 = o2 && prd_matches wildcards a1 a2 && prd_matches wildcards b1 b2
  | Bind (b1, _, body1), Bind (b2, _, body2) ->
    b1 = b2 && prd_matches wildcards body1 body2
  | Mem (es1, e1), Mem (es2, e2) ->
    List.length es1 = List.length es2 &&
    List.for_all2 (exp_matches wildcards) es1 es2 && exp_matches wildcards e1 e2
  | Eq (a1, b1), Eq (a2, b2)
  | Leq (a1, b1), Leq (a2, b2) ->
    exp_matches wildcards a1 a2 && exp_matches wildcards b1 b2
  | _ -> false

let ins_heart_resolve ctx =
  let rec count_bind_vars = function
    | Bind (Forall2, xs, inner) ->
      List.length xs + count_bind_vars inner
    | _ -> 0
  in
  let rec collect_bind_vars = function
    | Bind (Forall2, xs, inner) ->
      List.fold_right SS.add xs (collect_bind_vars inner)
    | _ -> SS.empty
  in
  let rec extract_neg_body = function
    | Bind (Forall2, _, inner) -> extract_neg_body inner
    | Unary (Not, body) -> Some body
    | _ -> None
  in
  let find_matching_hyps wildcards leaves entries =
    let find_match leaf =
      List.find_opt (fun (_, p) ->
        (match leaf with Leq _ -> false | _ -> true) &&
        prd_matches wildcards leaf p
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
  (* Collect all non-∀₂ entries as potential conjunct matches *)
  let other_entries = List.filter (fun (_, p) ->
    match p with Bind (Forall2, _, _) -> false | _ -> true
  ) ctx.entries in
  let rec scan = function
    | [] -> None
    | (name, (Bind (Forall2, _, _) as p)) :: rest ->
      let n_vars = count_bind_vars p in
      let wildcards = collect_bind_vars p in
      begin match extract_neg_body p with
      | Some body ->
        let leaves = conj_leaves body in
        begin match find_matching_hyps wildcards leaves other_entries with
        | Some conjs when conjs <> [] ->
          Some (build_term name n_vars conjs)
        | _ -> scan rest
        end
      | None -> scan rest
      end
    | _ :: rest -> scan rest
  in
  scan ctx.entries

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
      raise (Emit_admit "INS could not resolve contradiction")

(* ---- NRM1 compound ♢ emission ---- *)

let nrm1_extra_count goal =
  match goal with
  | Binary (Imp, Bind (_, xs, body), _) when List.length xs > 1 ->
    let fv = free_vars_of_prd body in
    let extra = List.tl xs in
    if List.exists (fun v ->
      SS.mem v fv.prop_vars || SS.mem v fv.exp_vars) extra
    then 0 else List.length extra
  | _ -> 0

(* ---- Result computation ---- *)

let rec compute_result (node : proof_node) : prd =
  match node with
  | Apply { rule; goal; children; _ } ->
    let base = strip_suffix rule in
    match base, children with
    | "STOP", [] -> goal
    | _, [child] when is_hoas_identity base -> compute_result child
    | ("AND2" | "AND3" | "AND5" | "OR4" | "VR3" | "VR2" | "EVR2"
      | "NOT1" | "NOT2" | "OR1" | "IMP1" | "IMP5" | "FX1"
      | "XST7" | "EVR3" | "OPR1" | "OPR2" | "AR9"), [child] ->
      compute_result child
    | ("AND1" | "OR3" | "AND4" | "IMP3" | "OR2" | "IMP2"
      | "EQV1" | "EQV2" | "EQV3" | "EQV4"), [child1; child2] ->
      Binary (And, compute_result child1, compute_result child2)
    | "IMP4", [child] ->
      let p = match goal with Binary (Imp, p, _) -> p | _ -> goal in
      Binary (Imp, p, compute_result child)
    | "ALL8", [child] ->
      let vars = match goal with Bind (_, xs, _) -> xs | _ -> [] in
      Bind (Bang, vars, compute_result child)
    | "ALL9", [child] ->
      let h = match goal with Binary (Imp, h, _) -> h | _ -> goal in
      Binary (Imp, h, compute_result child)
    | _ -> goal

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

