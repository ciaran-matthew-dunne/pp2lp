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

let is_hoas_identity = Rule_db.is_hoas_identity

(* Extract the binder variables from a goal of shape
   [ Bind | ¬Bind | Bind ⇒ _ | ¬Bind ⇒ _ ]. *)
let binding_vars = function
  | Binary (Imp, Bind (_, xs, _), _)
  | Binary (Imp, Unary (Not, Bind (_, xs, _)), _)
  | Bind (_, xs, _)
  | Unary (Not, Bind (_, xs, _)) -> xs
  | _ -> []

let goal_binding_count goal = List.length (binding_vars goal)

(* Tuple-uniform rule library: every rule is polymorphic in `[n]` over
   `Tuple n`, so we never need a per-arity variant. `select_variant`
   collapses to identity. *)
let select_variant rule _goal _children _flat = rule

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

(* introduce is only reached from emit_node (preorder, no _1 rules), so
   we only look up the base rule name. *)
let introduces_antecedent = Rule_db.intro_antecedent

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
      (* Tuple-uniform `!!` form: introduce a single variable of
         type `Tuple n` named after the first bound var. The body's
         references to original PP variables have already been
         substituted with `Prj k v` by `pp_lp`'s Bind renderer. *)
      let _ = flat in  (* arity collapse no longer relevant *)
      let v_name = match xs with x :: _ -> x ^ "_t" | [] -> "v" in
      Buffer.add_string buf ";\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "assume ";
      pp_ident buf v_name;
      push_tuple_binder ctx v_name xs
    | _ -> ctx
  end
  else ctx

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
  let rec total_arity = function
    | Bind (_, xs, body) -> List.length xs + total_arity body
    | _ -> 0
  in
  let rec search = function
    | [] -> None
    | (name, (Bind _ as p)) :: rest ->
      let rec scan = function
        | Bind (_, _, body) -> scan body
        | p -> p
      in
      if has_true_and (scan p) then Some (name, total_arity p)
      else search rest
    | _ :: rest -> search rest
  in
  (* Tuple-uniform AXM9 takes (v : Tuple n) (h : ...). Look up an
     in-scope Tuple-n binder of the matching arity and pass it as the
     witness. Falls back to `_` if none found. *)
  let emit_witness arity =
    match find_tuple_binder ctx arity with
    | Some (vname, _) -> Buffer.add_char buf ' '; pp_ident buf vname
    | None            -> Buffer.add_string buf " _"
  in
  match search ctx.entries with
  | Some (name, arity) ->
    emit_witness arity;
    Buffer.add_char buf ' ';
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

let emit_quant_r_args buf ctx rule node =
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
      (* lambda_vars and inner_vars bind names that may shadow outer
         tuple binders. Only outer-tuple names truly free in r_body need
         the projection rewrite. *)
      let r_body' =
        tuple_subst_prd_excluding ctx (lambda_vars @ inner_vars) r_body in
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
        pp_prd buf r_body';
        Buffer.add_char buf ')'
      end else
        pp_prd buf r_body';
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

let emit_ar3_args buf ctx node =
  (* AR3 (a : τ ι) : π ((𝟏 - a ≤ 𝟎) ⇒ R) → π (¬ (a ≤ 𝟎) ⇒ R).
     PP replay format [AR3(a | 1-a)] supplies `a` (first) and solver
     result 1-a (second, not needed by LP: baked into the signature). *)
  match node with
  | Apply { arg = Some (PipeArg (a_expr, _result_expr)); _ } ->
    Buffer.add_string buf " (";
    pp_exp buf (tuple_subst_exp ctx a_expr);
    Buffer.add_string buf ")"
  | _ ->
    raise (Emit_admit "AR3 missing pipe arg")

let emit_ar4_args buf ctx _goal =
  let found = List.find_opt (fun (_name, p) ->
    match p with Leq (_, Nat 0) -> true | _ -> false
  ) ctx.entries in
  match found with
  | Some (name, Leq (f_expr, _)) ->
    Buffer.add_string buf " (";
    pp_exp buf (tuple_subst_exp ctx f_expr);
    Buffer.add_string buf ") ";
    Buffer.add_string buf name;
    (* Third arg is π ((E + F) > 𝟎) — a solver side-condition that can
       only be discharged by trust (AR4's body is admit anyway). *)
    Buffer.add_string buf " trust"
  | _ ->
    raise (Emit_admit "AR4 could not find F ≤ 0 hypothesis")

let emit_ar56_args buf =
  Buffer.add_string buf " trust"

let emit_ar78_args buf ctx base (node : proof_node) =
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
      pp_exp buf (tuple_subst_exp ctx e);
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
    | Some (hyp_name, _witness_exps) ->
      (* Tuple-uniform NRM19 takes a single Tuple n witness. The
         binder's arity equals `List.length bvars`; pull a matching
         in-scope Tuple-n binder if there is one, else `_`. *)
      let arity = List.length bvars in
      (match find_tuple_binder ctx arity with
       | Some (vname, _) -> Buffer.add_char buf ' '; pp_ident buf vname
       | None            -> Buffer.add_string buf " _");
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
        pp_prd buf (tuple_subst_prd ctx p);
        Buffer.add_string buf ") trust"
      | _ ->
        raise (Emit_admit "AR9 missing solver arg")
      end
    | Some "dynamic:opr1" -> emit_opr_args buf node
    | Some "dynamic:opr2" -> emit_opr_args buf node
    | Some "dynamic:hyp" ->
      begin match find_axm_hyp ctx base goal with
      | Some name -> Buffer.add_char buf ' '; Buffer.add_string buf name
      | None -> Buffer.add_string buf " _"
      end
    | Some "dynamic:axm9" -> emit_axm9_args buf ctx
    | Some "dynamic:all7" | Some "dynamic:xst8" ->
      emit_quant_r_args buf ctx eff_rule node
    | Some "dynamic:ar3" -> emit_ar3_args buf ctx node
    | Some "dynamic:ar4" -> emit_ar4_args buf ctx goal
    | Some "dynamic:ar56" -> emit_ar56_args buf
    | Some "dynamic:ar78" -> emit_ar78_args buf ctx base node
    | Some "dynamic:nrm19" -> emit_nrm19_args buf ctx goal
    | _ when primed ->
      begin match ea with
      | Some args when not (String.starts_with ~prefix:"dynamic:" args) ->
        Buffer.add_char buf ' ';
        Buffer.add_string buf args
      | _ -> ()
      end
    | Some args ->
      Buffer.add_char buf ' ';
      Buffer.add_string buf args
    | None -> ()

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
