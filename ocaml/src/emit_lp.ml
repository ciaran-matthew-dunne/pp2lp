open Syntax_pp
open Proof_tree

(* ---- Identifier emission ---- *)

(* Lambdapi needs {|...|} escaping for identifiers with special chars *)
let is_simple_ident s =
  s <> "" &&
  (let c = s.[0] in (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_') &&
  String.to_seq s |> Seq.for_all (fun c ->
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
    (c >= '0' && c <= '9') || c = '_' || c = '\'')

let pp_ident buf s =
  if is_simple_ident s then Buffer.add_string buf s
  else begin
    Buffer.add_string buf "{|";
    Buffer.add_string buf s;
    Buffer.add_string buf "|}"
  end

(* ---- Expression pretty-printing (shallow encoding) ---- *)

let rec pp_exp buf e =
  match e with
  | Var "VRAI" | Var "TRUE" -> Buffer.add_string buf "BTRUE"
  | Var "FAUX" | Var "FALSE" -> Buffer.add_string buf "BFALSE"
  | Var s -> pp_ident buf s
  | Nat 0 -> Buffer.add_string buf "\xf0\x9d\x9f\x8e" (* 𝟎 *)
  | Nat 1 -> Buffer.add_string buf "\xf0\x9d\x9f\x8f" (* 𝟏 *)
  | Nat n ->
    Buffer.add_char buf '(';
    for _ = 1 to n - 1 do
      Buffer.add_string buf "\xf0\x9d\x9f\x8f + "
    done;
    Buffer.add_string buf "\xf0\x9d\x9f\x8f";
    Buffer.add_char buf ')'
  | App (f, args) ->
    Buffer.add_string buf "(eapp ";
    pp_ident buf f;
    Buffer.add_char buf ' ';
    pp_exp_args buf args;
    Buffer.add_char buf ')'
  | AOp (Add, e1, e2) ->
    Buffer.add_char buf '(';
    pp_exp buf e1;
    Buffer.add_string buf " + ";
    pp_exp buf e2;
    Buffer.add_char buf ')'
  | AOp (Sub, e1, e2) ->
    Buffer.add_char buf '(';
    pp_exp buf e1;
    Buffer.add_string buf " - ";
    pp_exp buf e2;
    Buffer.add_char buf ')'
  | Neg e1 ->
    Buffer.add_string buf "(\xe2\x80\x94 "; (* — (em dash = unary minus in B.lp) *)
    pp_exp buf e1;
    Buffer.add_char buf ')'
  | SetImage (e1, e2) ->
    Buffer.add_string buf "(eapp set_image (";
    pp_exp buf e1;
    Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
    pp_exp buf e2;
    Buffer.add_string buf "))"
  | Inter (e1, e2) ->
    Buffer.add_string buf "(eapp inter (";
    pp_exp buf e1;
    Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
    pp_exp buf e2;
    Buffer.add_string buf "))"
  | Union (e1, e2) ->
    Buffer.add_string buf "(eapp union (";
    pp_exp buf e1;
    Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
    pp_exp buf e2;
    Buffer.add_string buf "))"

and pp_exp_args buf = function
  | [e] -> pp_exp buf e
  | e :: rest ->
    Buffer.add_char buf '(';
    pp_exp buf e;
    List.iter (fun e' ->
      Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
      pp_exp buf e') rest;
    Buffer.add_char buf ')'
  | [] -> Buffer.add_string buf "\xf0\x9d\x9f\x8e" (* 𝟎 as fallback *)

(* ---- Conjunction flattening ---- *)

(* Flatten a left-associative And tree into a list of conjuncts *)
let rec flatten_conj = function
  | Binary (And, p1, p2) -> flatten_conj p1 @ flatten_conj p2
  | p -> [p]

(* Emit a list of conjuncts right-associatively: a ∧ (b ∧ (c ∧ d)) *)
let rec pp_conj_right buf = function
  | [p] -> pp_prd buf p
  | p :: rest ->
    Buffer.add_char buf '(';
    pp_prd buf p;
    Buffer.add_string buf " \xe2\x88\xa7 "; (* ∧ *)
    pp_conj_right buf rest;
    Buffer.add_char buf ')'
  | [] -> Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)

(* ---- Predicate pretty-printing (shallow encoding) ---- *)

and pp_prd buf p =
  match p with
  | Lift (Var "VRAI") | Lift (Var "TRUE") ->
    Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | Lift (Var "FAUX") | Lift (Var "FALSE") ->
    Buffer.add_string buf "\xe2\x8a\xa5" (* ⊥ *)
  | Lift (App (f, args)) ->
    (* In B, f(x) in predicate position is membership: x ϵ f *)
    Buffer.add_char buf '(';
    pp_exp_args buf args;
    Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
    pp_ident buf f;
    Buffer.add_char buf ')'
  | Lift (Var s) ->
    (* Free predicate variable — bare identifier *)
    pp_ident buf s
  | Lift e ->
    pp_exp buf e
  | Unary (Not, p1) ->
    Buffer.add_string buf "(\xc2\xac "; (* ¬ *)
    pp_prd buf p1;
    Buffer.add_char buf ')'
  | Binary (And, _, _) ->
    let elts = flatten_conj p in
    pp_conj_right buf elts
  | Binary (Or, p1, p2) ->
    Buffer.add_char buf '(';
    pp_prd buf p1;
    Buffer.add_string buf " \xe2\x88\xa8 "; (* ∨ *)
    pp_prd buf p2;
    Buffer.add_char buf ')'
  | Binary (Imp, p1, p2) ->
    Buffer.add_char buf '(';
    pp_prd buf p1;
    Buffer.add_string buf " \xe2\x87\x92 "; (* ⇒ *)
    pp_prd buf p2;
    Buffer.add_char buf ')'
  | Binary (Iff, p1, p2) ->
    Buffer.add_char buf '(';
    pp_prd buf p1;
    Buffer.add_string buf " \xe2\x87\x94 "; (* ⇔ *)
    pp_prd buf p2;
    Buffer.add_char buf ')'
  | Binary (Eq, p1, p2) ->
    Buffer.add_char buf '(';
    pp_prd buf p1;
    Buffer.add_string buf " \xe2\x87\x94 "; (* ⇔ *)
    pp_prd buf p2;
    Buffer.add_char buf ')'
  | Eq (e1, e2) ->
    Buffer.add_char buf '(';
    pp_exp buf e1;
    Buffer.add_string buf " = ";
    pp_exp buf e2;
    Buffer.add_char buf ')'
  | Leq (e1, e2) ->
    Buffer.add_char buf '(';
    pp_exp buf e1;
    Buffer.add_string buf " \xe2\x89\xa4 "; (* ≤ *)
    pp_exp buf e2;
    Buffer.add_char buf ')'
  | Mem (es, e) ->
    Buffer.add_char buf '(';
    pp_exp_args buf es;
    Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
    pp_exp buf e;
    Buffer.add_char buf ')'
  (* Quantifiers: HOAS style — `∀ x : τ ι, body *)
  | Bind (binder, xs, body) ->
    let qsym = match binder with
      | Forall0 -> "`\xe2\x88\x80" (* `∀ *)
      | Forall1 -> "`\xe2\x99\xa2"  (* `♢ *)
      | Forall2 -> "`\xe2\x99\xa1"  (* `♡ *)
      | Exists   -> "`\xe2\x88\x83"  (* `∃ *)
    in
    let rec emit_vars = function
      | [] -> pp_prd buf body
      | x :: rest ->
        Buffer.add_char buf '(';
        Buffer.add_string buf qsym;
        Buffer.add_char buf ' ';
        pp_ident buf x;
        Buffer.add_string buf " : \xcf\x84 \xce\xb9, "; (* τ ι *)
        emit_vars rest;
        Buffer.add_char buf ')'
    in
    emit_vars xs

(* Emit a list of predicates as a Lambdapi list literal: (a ∷ b ∷ c ∷ □) *)
let pp_prd_list buf prds =
  Buffer.add_char buf '(';
  List.iter (fun p ->
    pp_prd buf p;
    Buffer.add_string buf " \xe2\x88\xb7 " (* ∷ *)
  ) prds;
  Buffer.add_string buf "\xe2\x96\xa1"; (* □ *)
  Buffer.add_char buf ')'

let prd_to_string p =
  let buf = Buffer.create 256 in
  pp_prd buf p;
  Buffer.contents buf

let exp_to_string e =
  let buf = Buffer.create 64 in
  pp_exp buf e;
  Buffer.contents buf

(* ---- Free variable analysis ---- *)

module SS = Set.Make(String)

type free_vars = { prop_vars: SS.t; exp_vars: SS.t }

let empty_fv = { prop_vars = SS.empty; exp_vars = SS.empty }

let reserved = SS.of_list ["VRAI"; "TRUE"; "FAUX"; "FALSE"]

let rec collect_exp_fv bound fv = function
  | Var s when SS.mem s bound || SS.mem s reserved -> fv
  | Var s -> { fv with exp_vars = SS.add s fv.exp_vars }
  | Nat _ -> fv
  | AOp (_, e1, e2) -> collect_exp_fv bound (collect_exp_fv bound fv e1) e2
  | Neg e -> collect_exp_fv bound fv e
  | App (_, args) -> List.fold_left (collect_exp_fv bound) fv args
  | SetImage (e1, e2) | Inter (e1, e2) | Union (e1, e2) ->
    collect_exp_fv bound (collect_exp_fv bound fv e1) e2

let rec collect_prd_fv bound fv = function
  | Lift (Var s) when SS.mem s bound ->
    { fv with exp_vars = SS.add s fv.exp_vars }
  | Lift (Var s) when SS.mem s reserved -> fv
  | Lift (Var s) ->
    { fv with prop_vars = SS.add s fv.prop_vars }
  | Lift (App (f, args)) ->
    let fv = if SS.mem f bound || SS.mem f reserved then fv
             else { fv with exp_vars = SS.add f fv.exp_vars } in
    List.fold_left (collect_exp_fv bound) fv args
  | Lift e -> collect_exp_fv bound fv e
  | Unary (_, p) -> collect_prd_fv bound fv p
  | Binary (_, p1, p2) ->
    collect_prd_fv bound (collect_prd_fv bound fv p1) p2
  | Bind (_, xs, body) ->
    let bound' = List.fold_left (fun s x -> SS.add x s) bound xs in
    collect_prd_fv bound' fv body
  | Eq (e1, e2) | Leq (e1, e2) ->
    collect_exp_fv bound (collect_exp_fv bound fv e1) e2
  | Mem (es, e) ->
    collect_exp_fv bound (List.fold_left (collect_exp_fv bound) fv es) e

let free_vars_of_prd p = collect_prd_fv SS.empty empty_fv p

(* ---- Hypothesis extraction and pattern matching ---- *)

let rec collect_conj_hyps acc = function
  | Binary (And, l, r) ->
    collect_conj_hyps (collect_conj_hyps acc l) r
  | p -> p :: acc

let rec extract_theorem_hyps = function
  | Bind (Forall0, _, body) -> extract_theorem_hyps body
  | Binary (Imp, hyps, _) -> collect_conj_hyps [] hyps
  | _ -> []

(* ---- Hypothesis context for proof emission ---- *)

type hyp_ctx = {
  entries: (string * prd) list;  (* name, predicate *)
  counter: int;
}

let empty_ctx = { entries = []; counter = 0 }

let fresh_hyp ctx p =
  let name = Printf.sprintf "h%d" ctx.counter in
  let ctx' = { entries = (name, p) :: ctx.entries;
               counter = ctx.counter + 1 } in
  (name, ctx')

(* Search hypothesis context for a predicate matching target *)
let find_hyp ctx target =
  let rec search = function
    | [] -> None
    | (name, p) :: rest ->
      if p = target then Some name else search rest
  in
  search ctx.entries

(* Find hypothesis for an AXM rule based on rule name and goal *)
let find_axm_hyp ctx rule goal =
  match rule, goal with
  (* AXM1: π (¬ P) → π (P ⇒ Q) — need ¬P *)
  | "AXM1", Binary (Imp, p, _) -> find_hyp ctx (Unary (Not, p))
  (* AXM2: π P → π (¬ P ⇒ Q) — need P *)
  | "AXM2", Binary (Imp, Unary (Not, p), _) -> find_hyp ctx p
  (* AXM3: π P → π P — need P *)
  | "AXM3", p -> find_hyp ctx p
  (* AXM4: π R → π (P ⇒ R) — need R *)
  | "AXM4", Binary (Imp, _, r) -> find_hyp ctx r
  | "AXM4", p -> find_hyp ctx p  (* fallback: goal IS the hypothesis *)
  (* AXM5: π (¬ Q) → π (P ⇒ (Q ⇒ R)) — need ¬Q *)
  | "AXM5", Binary (Imp, _, Binary (Imp, q, _)) ->
    find_hyp ctx (Unary (Not, q))
  (* AXM6: π Q → π (P ⇒ (¬ Q ⇒ R)) — need Q *)
  | "AXM6", Binary (Imp, _, Binary (Imp, Unary (Not, q), _)) ->
    find_hyp ctx q
  (* NOT2: π P → π (¬P) = π (P → ⊥) — need the P that contradicts *)
  | "NOT2", Unary (Not, p) -> find_hyp ctx p
  | "NOT2", Binary (Imp, p, _) -> find_hyp ctx p
  | _ -> None

(* ---- AND5/AXM8 index computation ---- *)

(* Extract conjunction list from the antecedent of an implication goal *)
let conj_list_of_goal = function
  | Binary (Imp, ante, _) -> flatten_conj ante
  | _ -> []

(* Find AND5 indices: j = index of (a ⇒ b), i = index of a.
   We compare the parent goal with the child goal to find which
   implication was eliminated. *)
let find_and5_indices (goal : prd) (child_goal : prd) =
  let parent_list = conj_list_of_goal goal in
  let child_list = conj_list_of_goal child_goal in
  (* The child list is rem_nth parent j ++ [b].
     Find the element in parent that's missing from child (that's at index j).
     The new element appended to child is b. *)
  let n = List.length parent_list in
  (* Find index j: the element in parent_list not in child_list prefix *)
  let rec find_j pi ci j =
    if pi >= n then None
    else
      let p_elt = List.nth parent_list pi in
      if ci < List.length child_list && p_elt = List.nth child_list ci then
        find_j (pi + 1) (ci + 1) j
      else
        (* This is the removed element at index pi *)
        Some pi
  in
  match find_j 0 0 0 with
  | None -> None
  | Some j ->
    let removed = List.nth parent_list j in
    (* removed should be (a ⇒ b) *)
    match removed with
    | Binary (Imp, a, _b) ->
      (* Find index i where a appears in parent_list *)
      let rec find_i idx = function
        | [] -> None
        | elt :: rest ->
          if elt = a && idx <> j then Some idx
          else find_i (idx + 1) rest
      in
      begin match find_i 0 parent_list with
      | Some i -> Some (i, j)
      | None -> None
      end
    | _ -> None

(* Find AXM8 index: which conjunct is equal to r (the consequent) *)
let find_axm8_index (goal : prd) =
  let conjs = conj_list_of_goal goal in
  let r = match goal with Binary (Imp, _, r) -> Some r | _ -> None in
  match r with
  | None -> None
  | Some r ->
    let rec find idx = function
      | [] -> None
      | elt :: rest ->
        if elt = r then Some idx
        else find (idx + 1) rest
    in
    find 0 conjs

(* Emit a natural number literal *)
let emit_nat buf n =
  Buffer.add_char buf ' ';
  Buffer.add_string buf (string_of_int n)

(* ---- Rule argument emission ---- *)

let emit_rule_args buf _thm_hyps ctx eff_rule (node : proof_node) =
  match node with
  | Apply { rule = _; goal; _ } ->
    let rule = eff_rule in
    let is_primed =
      String.length rule > 2
      && String.sub rule (String.length rule - 2) 2 = "_1"
    in
    let base_rule =
      if is_primed
      then String.sub rule 0 (String.length rule - 2)
      else rule
    in
    (* Primed (_1) variants take equality proofs, not ⊤ᵢ.
       Their single premise is always inferred via _. *)
    if is_primed then ()
    else
    (* Check JSON emit_args for this rule *)
    let db = Rule_db.get () in
    let ea = Rule_db.emit_args db base_rule in
    match ea with
    (* Dynamic argument handlers *)
    | Some "dynamic:hyp" ->
      begin match find_axm_hyp ctx base_rule goal with
      | Some name ->
        Buffer.add_char buf ' ';
        Buffer.add_string buf name
      | None ->
        Buffer.add_string buf " _"
      end

    | Some "dynamic:axm8" ->
      let conjs = conj_list_of_goal goal in
      begin match find_axm8_index goal with
      | Some i ->
        Buffer.add_char buf ' ';
        pp_prd_list buf conjs;
        emit_nat buf i;
        Buffer.add_string buf " (\xce\xbb x, x)" (* λ x, x *)
      | None -> Buffer.add_string buf " _"
      end

    | Some "dynamic:axm9" ->
      let hyp_result =
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
            if has_true_and body then
              Some (name, count_bind_depth p)
            else search rest
          | _ :: rest -> search rest
        in
        search ctx.entries
      in
      begin match hyp_result with
      | Some (name, nvars) when nvars >= 2 ->
        Buffer.add_string buf "_2 _ _ ";
        Buffer.add_string buf name
      | Some (name, _) ->
        Buffer.add_string buf " _ ";
        Buffer.add_string buf name
      | None ->
        Buffer.add_string buf " _ _"
      end

    | Some "dynamic:and5" ->
      let children = match node with Apply { children; _ } -> children in
      let child_goal = match children with
        | [Apply { goal; _ }] -> Some goal
        | _ -> None
      in
      begin match child_goal with
      | Some cg ->
        begin match find_and5_indices goal cg with
        | Some (i, j) ->
          let conjs = conj_list_of_goal goal in
          let imp_elt = List.nth conjs j in
          let (a_prd, b_prd) = match imp_elt with
            | Binary (Imp, a, b) -> (a, b)
            | _ -> failwith "AND5: element at j is not an implication"
          in
          Buffer.add_char buf ' ';
          pp_prd_list buf conjs;
          Buffer.add_char buf ' ';
          pp_prd buf a_prd;
          Buffer.add_char buf ' ';
          pp_prd buf b_prd;
          emit_nat buf i;
          emit_nat buf j;
          Buffer.add_string buf " (eq_refl _) (eq_refl _)"
        | None ->
          Buffer.add_string buf " _ _ _ _ (eq_refl _) (eq_refl _)"
        end
      | None ->
        Buffer.add_string buf " _ _ _ _ (eq_refl _) (eq_refl _)"
      end

    | Some "dynamic:all7" | Some "dynamic:xst8" ->
      begin match node with
      | Apply { children; _ } ->
        let r_opt = match children with
          | [_; Apply { goal = Binary (Imp, Bind (Forall1, xs, r_body), _); _ }] ->
            if rule = "ALL7_2" then
              Some (xs, [], r_body)
            else
              let lambda_vars = (match xs with x :: _ -> [x] | [] -> []) in
              let inner_vars = (match xs with _ :: rest -> rest | [] -> []) in
              Some (lambda_vars, inner_vars, r_body)
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
              Buffer.add_string buf " : \xcf\x84 \xce\xb9, " (* : τ ι,  *)
            ) inner_vars;
            pp_prd buf r_body;
            Buffer.add_char buf ')'
          end else
            pp_prd buf r_body;
          Buffer.add_char buf ')'
        | None -> ()
        end
      end

    (* Static args from JSON (e.g. "⊤ᵢ", "⊤ᵢ ⊤ᵢ", "_ _ ⊤ᵢ ⊤ᵢ") *)
    | Some args ->
      Buffer.add_char buf ' ';
      Buffer.add_string buf args

    (* No args *)
    | None -> ()

(* ---- Proof node emission ---- *)

let effective_rule_name _hyps (node : proof_node) =
  match node with
  | Apply { rule; _ } -> rule

let emit_refine_rule buf rule =
  Buffer.add_string buf "refine ";
  Buffer.add_string buf rule

(* Extract the antecedent of an implication from a goal predicate *)
let imp_antecedent = function
  | Binary (Imp, p, _) -> Some p
  | _ -> None

let rec emit_node buf thm_hyps ctx indent ?(inline=false) ?(flat=0) (node : proof_node) =
  match node with
  | Apply { rule = _; arg = node_arg; goal; children; _ } ->
    let rule = effective_rule_name thm_hyps node in
    let pad = String.make indent ' ' in
    let first_pad = if inline then "" else pad in
    begin match children with
    | [] when rule = "SORRY" ->
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "admit"

    | [] ->
      (* Leaf *)
      Buffer.add_string buf first_pad;
      emit_refine_rule buf rule;
      emit_rule_args buf thm_hyps ctx rule node

    | [child] when Proof_tree.is_branching_quantifier rule ->
      (* ALL7/XST8 with only primed child *)
      Buffer.add_string buf first_pad;
      emit_refine_rule buf rule;
      emit_rule_args buf thm_hyps ctx rule node;
      Buffer.add_string buf " _ _\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "{ ";
      emit_node buf thm_hyps ctx (indent + 2) ~inline:true child;
      Buffer.add_string buf " }\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "{ admit }"

    | [Apply { rule = child_rule; children = [grandchild]; _ } as _child]
      when rule = "NRM8" && child_rule = "NRM13" ->
      (* NRM8 + NRM13 combined: count total ∀ variables *)
      let nrm_rule =
        (* Count variables in the goal's leading quantifier chain *)
        let rec count_bind_vars = function
          | Binary (Imp, Bind (_, xs, body), _) ->
            List.length xs + count_bind_vars_inner body
          | _ -> 0
        and count_bind_vars_inner = function
          | Bind (_, xs, body) -> List.length xs + count_bind_vars_inner body
          | Binary (Imp, _, _) -> 0
          | _ -> 0
        in
        let n = count_bind_vars goal in
        if n >= 3 then "NRM8_13_3"
        else "NRM8_13"
      in
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf nrm_rule;
      Buffer.add_string buf " \xe2\x8a\xa4\xe1\xb5\xa2 _";
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx indent grandchild

    | [child] when rule = "XST5" ->
      (* XST5 on compound ∃: use XST5_2 for 2-var compounds *)
      let actual_rule = match goal with
        | Binary (Imp, Unary (Not, Bind (Exists, xs, _)), _)
          when List.length xs >= 2 -> "XST5_2"
        | _ -> "XST5"
      in
      Buffer.add_string buf first_pad;
      emit_refine_rule buf actual_rule;
      emit_rule_args buf thm_hyps ctx actual_rule node;
      Buffer.add_string buf " _";
      let child_flat = if actual_rule = "XST5_2" then 0 else flat + 1 in
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx indent ~flat:child_flat child

    | [child] when rule = "XST6" ->
      (* XST6 on compound ∃: use XST6_2 for 2-var compounds *)
      let actual_rule = match goal with
        | Unary (Not, Bind (Exists, xs, _)) when List.length xs >= 2 -> "XST6_2"
        | _ -> "XST6"
      in
      Buffer.add_string buf first_pad;
      emit_refine_rule buf actual_rule;
      emit_rule_args buf thm_hyps ctx actual_rule node;
      Buffer.add_string buf " _";
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx indent child

    | [child] when (rule = "NRM14" || rule = "NRM15") ->
      (* NRM14/NRM15 on compound ♢: use _2 variant for 2-var compounds *)
      let actual_rule = match goal with
        | Binary (Imp, Bind (_, xs, _), _) when List.length xs >= 2 ->
          rule ^ "_2"
        | _ -> rule
      in
      Buffer.add_string buf first_pad;
      emit_refine_rule buf actual_rule;
      emit_rule_args buf thm_hyps ctx actual_rule node;
      Buffer.add_string buf " _;\n";
      emit_node buf thm_hyps ctx indent child

    | [child] when rule = "NRM1" ->
      (* NRM1: strips one ♢ level. For compound ♢(x,y,...) where the body
         doesn't use the extra variables, need extra NRM1s. *)
      let extra_nrm1 = match goal with
        | Binary (Imp, Bind (_, xs, body), _) when List.length xs > 1 ->
          (* Only add extra NRM1 if body doesn't use the extra vars *)
          let fv = free_vars_of_prd body in
          let extra = List.tl xs in
          let body_uses_extra = List.exists (fun v ->
            SS.mem v fv.prop_vars || SS.mem v fv.exp_vars) extra in
          if body_uses_extra then 0
          else List.length extra
        | _ -> 0
      in
      Buffer.add_string buf first_pad;
      emit_refine_rule buf rule;
      emit_rule_args buf thm_hyps ctx rule node;
      Buffer.add_string buf " _";
      for _ = 1 to extra_nrm1 do
        Buffer.add_string buf ";\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "refine NRM1 _"
      done;
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx indent ~flat:0 child

    | [child] ->
      (* Single child — sequential *)
      Buffer.add_string buf first_pad;
      emit_refine_rule buf rule;
      emit_rule_args buf thm_hyps ctx rule node;
      Buffer.add_string buf " _";
      (* IMP4 introduces a hypothesis *)
      let ctx' =
        if rule = "IMP4" || rule = "IMP4_1" then begin
          match imp_antecedent goal with
          | Some p ->
            let (name, ctx') = fresh_hyp ctx p in
            Buffer.add_string buf ";\n";
            Buffer.add_string buf pad;
            Buffer.add_string buf "assume ";
            Buffer.add_string buf name;
            ctx'
          | None -> ctx
        end else ctx
      in
      (* ALL9: introduces the ♡-hypothesis via ⇒ → function type *)
      let ctx' =
        if rule = "ALL9" then begin
          match imp_antecedent goal with
          | Some p ->
            let (name, ctx') = fresh_hyp ctx' p in
            Buffer.add_string buf ";\n";
            Buffer.add_string buf pad;
            Buffer.add_string buf "assume ";
            Buffer.add_string buf name;
            ctx'
          | None -> ctx'
        end else ctx'
      in
      (* ALL8: introduces bound variables.
         If flattening rules consumed some ∀ levels (flat > 0),
         assume fewer variables. *)
      let () =
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
        end
      in
      (* Propagate flat count for rules that split compound bindings.
         ALL5 and XST5 peel one level from a compound binding.
         ALL1-4, ALL6, XST1-4 are identity in HOAS and pass through. *)
      let child_flat =
        match rule with
        | "ALL5" | "XST5" | "XST7" -> flat + 1
        | "ALL1" | "ALL2" | "ALL3" | "ALL4" | "ALL6"
        | "XST1" | "XST2" | "XST3" | "XST4" -> flat
        | _ -> 0
      in
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx' indent ~flat:child_flat child

    | [child1; child2] when Proof_tree.is_branching_quantifier rule ->
      (* ALL7/XST8: first child needs assume for bound vars *)
      (* Use ALL7_2 when the HOAS goal has ∀x.∀y at top level.
         This is the case when the compound binding has 2+ vars and
         no splitting rule (ALL5/XST5) has consumed a level (flat=0). *)
      let eff_rule =
        if rule = "ALL7" then
          match goal with
          | Binary (Imp, Bind (_, xs, _), _)
            when List.length xs >= 2 && flat = 0 -> "ALL7_2"
          | _ -> rule
        else rule
      in
      Buffer.add_string buf first_pad;
      emit_refine_rule buf eff_rule;
      emit_rule_args buf thm_hyps ctx eff_rule node;
      Buffer.add_string buf " _ _\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "{ ";
      (* Extract bound vars from the ∀/∃ in the goal's antecedent.
         In HOAS, ALL7/XST8 handles 1 variable. For compound bindings,
         extra variables are introduced via ALL8_1 if R uses them. *)
      let bvars = match goal with
        | Binary (Imp, Bind (_, xs, _), _) ->
          (* For ALL7 (1 var), only assume the first variable.
             For ALL7_2 (2 vars), assume all compound variables. *)
          if eff_rule = "ALL7" && List.length xs > 1 then
            (match xs with x :: _ -> [x] | [] -> [])
          else xs
        | _ -> []
      in
      if bvars <> [] then begin
        Buffer.add_string buf "assume";
        List.iter (fun x ->
          Buffer.add_char buf ' ';
          pp_ident buf x) bvars;
        Buffer.add_string buf "; "
      end;
      emit_node buf thm_hyps ctx (indent + 2) ~inline:true child1;
      Buffer.add_string buf " }\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "{ ";
      emit_node buf thm_hyps ctx (indent + 2) ~inline:true child2;
      Buffer.add_string buf " }"

    | [child1; child2] ->
      (* Two children — branching *)
      Buffer.add_string buf first_pad;
      emit_refine_rule buf rule;
      emit_rule_args buf thm_hyps ctx rule node;
      Buffer.add_string buf " _ _\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "{ ";
      emit_node buf thm_hyps ctx (indent + 2) ~inline:true child1;
      Buffer.add_string buf " }\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "{ ";
      emit_node buf thm_hyps ctx (indent + 2) ~inline:true child2;
      Buffer.add_string buf " }"

    | _ ->
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "admit (* too many children *)"
    end

(* ---- Full .lp file generation ---- *)

let lp_header = "require open pp2lp.B pp2lp.Rules;\n"

let emit_symbol (name : string) (goal : prd) (tree : proof_node) : string =
  let buf = Buffer.create 4096 in
  let thm_hyps = extract_theorem_hyps goal in
  let fv = free_vars_of_prd goal in

  (* Symbol declaration with free variable parameters *)
  Buffer.add_string buf "opaque symbol ";
  Buffer.add_string buf name;

  (* Emit parameter lists *)
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

  (* Type annotation *)
  Buffer.add_string buf " :\n  \xcf\x80 ("; (* π *)
  pp_prd buf goal;
  Buffer.add_string buf ") \xe2\x89\x94\n"; (* ≔ *)

  (* Proof body *)
  Buffer.add_string buf "begin\n";

  (* Assume all parameters *)
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

(* Backwards compat: emit header + single symbol *)
let emit_lp (name : string) (goal : prd) (tree : proof_node) : string =
  lp_header ^ "\n" ^ emit_symbol name goal tree
