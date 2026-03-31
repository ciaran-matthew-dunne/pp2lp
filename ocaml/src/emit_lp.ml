open Syntax_pp
open Proof_tree

(* ---- Identifier emission ---- *)

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
    Buffer.add_string buf "(\xe2\x80\x94 "; (* — *)
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

(* ---- Conjunction helpers ---- *)

let rec flatten_conj = function
  | Binary (And, p1, p2) -> flatten_conj p1 @ [p2]
  | p -> [p]

let rec pp_conj_left buf = function
  | [] -> Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | [p] -> pp_prd buf p
  | first :: rest ->
    List.iter (fun _ -> Buffer.add_char buf '(') rest;
    pp_prd buf first;
    List.iter (fun p ->
      Buffer.add_string buf " \xe2\x88\xa7 "; (* ∧ *)
      pp_prd buf p;
      Buffer.add_char buf ')'
    ) rest

(* ---- Predicate pretty-printing (shallow encoding) ---- *)

and pp_prd buf p =
  match p with
  | Lift (Var "VRAI") | Lift (Var "TRUE") ->
    Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | Lift (Var "FAUX") | Lift (Var "FALSE") ->
    Buffer.add_string buf "\xe2\x8a\xa5" (* ⊥ *)
  | Lift (App (f, args)) ->
    Buffer.add_char buf '(';
    pp_exp_args buf args;
    Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
    pp_ident buf f;
    Buffer.add_char buf ')'
  | Lift (Var s) ->
    pp_ident buf s
  | Lift e ->
    pp_exp buf e
  | Unary (Not, p1) ->
    Buffer.add_string buf "(\xc2\xac "; (* ¬ *)
    pp_prd buf p1;
    Buffer.add_char buf ')'
  | Binary (And, _, _) ->
    let elts = flatten_conj p in
    pp_conj_left buf elts
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

(* ---- Left-associative conjunction extraction/reconstruction ----
   For n conjuncts [c₀; c₁; ...; cₙ₋₁], left-assoc tree is:
     ((...(c₀ ∧ c₁) ∧ c₂) ∧ ...) ∧ cₙ₋₁

   Extraction of element k from proof variable var:
     k = 0:       ∧ₑ₁ (∧ₑ₁ (... var))     — (n-1) left projections
     k > 0, k<n-1: ∧ₑ₂ (∧ₑ₁^(n-1-k) var)  — lefts then right
     k = n-1:     ∧ₑ₂ var                   — just right projection
*)

let rec emit_e1_chain buf var n =
  if n = 0 then Buffer.add_string buf var
  else begin
    Buffer.add_string buf "\xe2\x88\xa7\xe2\x82\x91\xe2\x82\x81 "; (* ∧ₑ₁ *)
    if n > 1 then Buffer.add_char buf '(';
    emit_e1_chain buf var (n - 1);
    if n > 1 then Buffer.add_char buf ')'
  end

let emit_extract buf var n k =
  if n = 1 then Buffer.add_string buf var
  else
    let d = if k = 0 then n - 1 else n - 1 - k in
    if k > 0 then begin
      Buffer.add_string buf "\xe2\x88\xa7\xe2\x82\x91\xe2\x82\x82 "; (* ∧ₑ₂ *)
      if d > 0 then Buffer.add_char buf '(';
      emit_e1_chain buf var d;
      if d > 0 then Buffer.add_char buf ')'
    end else
      emit_e1_chain buf var d

let emit_conj_from_elts buf (elts : (Buffer.t -> unit) list) =
  match elts with
  | [] -> Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | [e] -> e buf
  | first :: rest ->
    List.iter (fun _ -> Buffer.add_string buf "(\xe2\x88\xa7\xe1\xb5\xa2 ") rest; (* ∧ᵢ *)
    first buf;
    List.iter (fun e ->
      Buffer.add_char buf ' ';
      e buf;
      Buffer.add_char buf ')'
    ) rest

let emit_and5_fwd buf var n i j =
  let elts = ref [] in
  for k = n - 1 downto 0 do
    if k <> j then
      elts := (fun buf -> Buffer.add_char buf '('; emit_extract buf var n k; Buffer.add_char buf ')') :: !elts
  done;
  elts := !elts @ [(fun buf ->
    Buffer.add_string buf "((";
    emit_extract buf var n j;
    Buffer.add_string buf ") (";
    emit_extract buf var n i;
    Buffer.add_string buf "))")];
  emit_conj_from_elts buf !elts

let emit_and5_bwd buf var n j =
  let n' = n in
  let elts = ref [] in
  for k = n - 1 downto 0 do
    if k < j then
      elts := (fun buf -> Buffer.add_char buf '('; emit_extract buf var n' k; Buffer.add_char buf ')') :: !elts
    else if k > j then
      elts := (fun buf -> Buffer.add_char buf '('; emit_extract buf var n' (k - 1); Buffer.add_char buf ')') :: !elts
    else
      elts := (fun buf ->
        Buffer.add_string buf "(\xce\xbb _, "; (* λ _, *)
        emit_extract buf var n' (n' - 1);
        Buffer.add_char buf ')') :: !elts
  done;
  emit_conj_from_elts buf !elts

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

(* ---- Hypothesis context ---- *)

let rec collect_conj_hyps acc = function
  | Binary (And, l, r) ->
    collect_conj_hyps (collect_conj_hyps acc l) r
  | p -> p :: acc

let rec extract_theorem_hyps = function
  | Bind (Forall0, _, body) -> extract_theorem_hyps body
  | Binary (Imp, hyps, _) -> collect_conj_hyps [] hyps
  | _ -> []

type hyp_ctx = {
  entries: (string * prd) list;
  counter: int;
}

let empty_ctx = { entries = []; counter = 0 }

let fresh_hyp ctx p =
  let name = Printf.sprintf "h%d" ctx.counter in
  let ctx' = { entries = (name, p) :: ctx.entries;
               counter = ctx.counter + 1 } in
  (name, ctx')

let find_hyp ctx target =
  let rec search = function
    | [] -> None
    | (name, p) :: rest ->
      if p = target then Some name else search rest
  in
  search ctx.entries

(* ---- AST substitution ---- *)

let rec subst_exp x y = function
  | Var s when s = x -> Var y
  | Var _ | Nat _ as e -> e
  | App (f, args) -> App (f, List.map (subst_exp x y) args)
  | AOp (op, e1, e2) -> AOp (op, subst_exp x y e1, subst_exp x y e2)
  | Neg e -> Neg (subst_exp x y e)
  | SetImage (e1, e2) -> SetImage (subst_exp x y e1, subst_exp x y e2)
  | Inter (e1, e2) -> Inter (subst_exp x y e1, subst_exp x y e2)
  | Union (e1, e2) -> Union (subst_exp x y e1, subst_exp x y e2)

let rec subst_prd x y = function
  | Lift e -> Lift (subst_exp x y e)
  | Unary (op, p) -> Unary (op, subst_prd x y p)
  | Binary (op, p1, p2) -> Binary (op, subst_prd x y p1, subst_prd x y p2)
  | Bind (b, xs, body) ->
    if List.mem x xs then Bind (b, xs, body)
    else Bind (b, xs, subst_prd x y body)
  | Mem (es, e) -> Mem (List.map (subst_exp x y) es, subst_exp x y e)
  | Eq (e1, e2) -> Eq (subst_exp x y e1, subst_exp x y e2)
  | Leq (e1, e2) -> Leq (subst_exp x y e1, subst_exp x y e2)

(* ---- Variant selection ----
   Selects the effective LP rule name based on goal shape and context.
   Handles _2 variants, NRM8+NRM13 fusion, and HOAS identity skip. *)

let is_hoas_identity = function
  | "ALL1" | "ALL2" | "ALL3" | "ALL4" | "ALL6"
  | "XST1" | "XST2" | "XST3" | "XST4"
  | "AR3_F" -> true
  | _ -> false

let binding_vars = function
  | Binary (Imp, Bind (_, xs, _), _) -> xs
  | Bind (_, xs, _) -> xs
  | _ -> []

let select_variant rule goal children flat =
  match rule, children with
  (* NRM8 + NRM13 fusion *)
  | "NRM8", [Apply { rule = "NRM13"; _ }] ->
    let rec count_vars = function
      | Binary (Imp, Bind (_, xs, body), _) ->
        List.length xs + count_inner body
      | _ -> 0
    and count_inner = function
      | Bind (_, xs, body) -> List.length xs + count_inner body
      | _ -> 0
    in
    if count_vars goal >= 3 then "NRM8_13_3" else "NRM8_13"
  (* ALL7/XST8: 2-var compound binding → _2 variant *)
  | "ALL7", _ ->
    begin match goal with
    | Binary (Imp, Bind (_, xs, _), _)
      when List.length xs >= 2 && flat = 0 -> "ALL7_2"
    | _ -> rule
    end
  | "XST8", _ ->
    begin match goal with
    | Bind (Exists, xs, _)
      when List.length xs >= 2 && flat = 0 -> "XST8_2"
    | _ -> rule
    end
  (* XST5/XST6: 2-var compound ∃ → _2 variant *)
  | "XST5", _ ->
    begin match goal with
    | Binary (Imp, Unary (Not, Bind (Exists, xs, _)), _)
      when List.length xs >= 2 -> "XST5_2"
    | _ -> rule
    end
  | "XST6", _ ->
    begin match goal with
    | Unary (Not, Bind (Exists, xs, _))
      when List.length xs >= 2 -> "XST6_2"
    | _ -> rule
    end
  (* NRM14/NRM15/NRM19: 2-var compound binding → _2 variant *)
  | ("NRM14" | "NRM15" | "NRM19"), _ ->
    begin match goal with
    | Binary (Imp, Bind (_, xs, _), _)
      when List.length xs >= 2 -> rule ^ "_2"
    | _ -> rule
    end
  | _ -> rule

(* ---- Child flat propagation ---- *)

let compute_child_flat rule flat =
  match rule with
  | "ALL5" | "XST5" | "XST7" -> flat + 1
  | "XST5_2" -> 0
  | _ when is_hoas_identity rule -> flat
  | _ -> 0

(* ---- Hypothesis/variable introduction ----
   Emits assume lines for IMP4, ALL9, ALL8 and returns updated context. *)

let introduce buf pad ctx rule goal flat =
  (* IMP4: introduce antecedent as hypothesis *)
  let ctx =
    if rule = "IMP4" || rule = "IMP4_1" then
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
  (* ALL9: introduce ♡-hypothesis *)
  let ctx =
    if rule = "ALL9" then
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
  (* ALL8: introduce bound variables (with flat adjustment) *)
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

let strip_suffix rule =
  let len = String.length rule in
  if len > 2 then
    let s = String.sub rule (len - 2) 2 in
    if s = "_1" || s = "_2" then String.sub rule 0 (len - 2)
    else rule
  else rule

let is_primed rule =
  let len = String.length rule in
  len > 2 && String.sub rule (len - 2) 2 = "_1"

(* AXM hypothesis lookup *)
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
  | "NOT2", Unary (Not, p) -> find_hyp ctx p
  | "NOT2", Binary (Imp, p, _) -> find_hyp ctx p
  | _ -> None

(* AXM8: extract i-th conjunct via lambda *)
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

(* AXM9: find ∀x.¬(⊤ ∧ ...) hypothesis, select _2 variant *)
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
    Buffer.add_string buf "_2 _ _ ";
    Buffer.add_string buf name
  | Some (name, _) ->
    Buffer.add_string buf " _ ";
    Buffer.add_string buf name
  | None ->
    Buffer.add_string buf " _ _"

(* AND5: forward/backward conjunction permutation lambdas *)
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

(* ALL7/XST8: emit R normalisation predicate lambda *)
let emit_quant_r_args buf rule node =
  match node with
  | Apply { children; _ } ->
    let r_opt = match children with
      | [_; Apply { goal = Binary (Imp, Bind ((Forall0|Forall1|Forall2), xs, r_body), _); _ }] ->
        if rule = "ALL7_2" || rule = "XST8_2" then
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
          Buffer.add_string buf " : \xcf\x84 \xce\xb9, " (* : τ ι, *)
        ) inner_vars;
        pp_prd buf r_body;
        Buffer.add_char buf ')'
      end else
        pp_prd buf r_body;
      Buffer.add_char buf ')'
    | None -> ()
    end

(* OPR1/OPR2: emit substitution predicate lambda *)
let emit_opr_args buf opr_rule goal =
  let decompose = match goal with
    | Binary (Imp, Eq (Var x, _), body) when opr_rule = "OPR1" -> Some (x, body)
    | Binary (Imp, Eq (_, Var x), body) when opr_rule = "OPR2" -> Some (x, body)
    | _ -> None
  in
  match decompose with
  | Some (x, body) ->
    let z = "__z" in
    let body' = subst_prd x z body in
    Buffer.add_string buf " (\xce\xbb "; (* (λ  *)
    Buffer.add_string buf z;
    Buffer.add_string buf ", ";
    pp_prd buf body';
    Buffer.add_char buf ')'
  | None ->
    Buffer.add_string buf " _"

(* NRM19: find witness and hypothesis for ♡-body instantiation *)
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
    let db = Rule_db.get () in
    let ea = Rule_db.emit_args db base in
    match ea with
    (* Shared primed+base handlers *)
    | Some "dynamic:axm8" -> emit_axm8_args buf goal
    | Some "dynamic:and5" -> emit_and5_args buf goal node ~primed
    | Some "dynamic:ar9" ->
      (* AR9/AR9_1: emit solver result F from rule arg, then ⊤ᵢ *)
      begin match arg with
      | Some (Pred p) ->
        Buffer.add_string buf " (";
        pp_prd buf p;
        Buffer.add_string buf ") \xe2\x8a\xa4\xe1\xb5\xa2"
      | _ ->
        Printf.eprintf "warning: AR9 missing solver arg\n";
        Buffer.add_string buf " _ \xe2\x8a\xa4\xe1\xb5\xa2"
      end
    (* Primed: emit static args if present, skip dynamic base-only handlers *)
    | _ when primed ->
      begin match ea with
      | Some args when not (String.length args > 8 && String.sub args 0 8 = "dynamic:") ->
        Buffer.add_char buf ' ';
        Buffer.add_string buf args
      | _ -> ()
      end
    (* Base-only handlers *)
    | Some "dynamic:hyp" ->
      begin match find_axm_hyp ctx base goal with
      | Some name -> Buffer.add_char buf ' '; Buffer.add_string buf name
      | None -> Buffer.add_string buf " _"
      end
    | Some "dynamic:axm9" -> emit_axm9_args buf ctx
    | Some "dynamic:all7" | Some "dynamic:xst8" ->
      emit_quant_r_args buf eff_rule node
    | Some "dynamic:opr1" -> emit_opr_args buf "OPR1" goal
    | Some "dynamic:opr2" -> emit_opr_args buf "OPR2" goal
    | Some "dynamic:nrm19" -> emit_nrm19_args buf ctx goal
    (* Static args from JSON *)
    | Some args ->
      Buffer.add_char buf ' ';
      Buffer.add_string buf args
    | None -> ()

(* ---- Proof node emission ---- *)

let rec emit_node buf thm_hyps ctx indent ?(inline=false) ?(flat=0)
    (node : proof_node) =
  match node with
  | Apply { rule; goal; children; _ } ->
    let pad = String.make indent ' ' in
    let first_pad = if inline then "" else pad in
    let eff_rule = select_variant rule goal children flat in
    begin match children with
    | [] when rule = "SORRY" ->
      Printf.eprintf "warning: emitting admit for incomplete proof\n";
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "admit"

    | [] ->
      (* Leaf *)
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf eff_rule;
      emit_rule_args buf ctx eff_rule node

    | [child] when is_hoas_identity rule ->
      (* ALL1-4, ALL6, XST1-4: skip entirely, just emit child *)
      let child_flat = compute_child_flat rule flat in
      emit_node buf thm_hyps ctx indent ~inline ~flat:child_flat child

    | [Apply { rule = "NRM13"; children = [grandchild]; _ }]
      when rule = "NRM8" ->
      (* NRM8 + NRM13 fused *)
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf eff_rule;
      Buffer.add_string buf " \xe2\x8a\xa4\xe1\xb5\xa2 _;\n"; (* ⊤ᵢ _ *)
      emit_node buf thm_hyps ctx indent grandchild

    | [child] when Proof_tree.is_branching_quantifier rule ->
      (* ALL7/XST8 with only primed child — admit second branch *)
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf rule;
      emit_rule_args buf ctx rule node;
      Buffer.add_string buf " _ _\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "{ ";
      emit_node buf thm_hyps ctx (indent + 2) ~inline:true child;
      Buffer.add_string buf " }\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "{ admit }"

    | [child] when rule = "NRM1" ->
      (* NRM1: extra applications for compound ♢(x,y,...) *)
      let extra = match goal with
        | Binary (Imp, Bind (_, xs, body), _) when List.length xs > 1 ->
          let fv = free_vars_of_prd body in
          let extra = List.tl xs in
          if List.exists (fun v ->
            SS.mem v fv.prop_vars || SS.mem v fv.exp_vars) extra
          then 0 else List.length extra
        | _ -> 0
      in
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "refine NRM1 _";
      for _ = 1 to extra do
        Buffer.add_string buf ";\n";
        Buffer.add_string buf pad;
        Buffer.add_string buf "refine NRM1 _"
      done;
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx indent child

    | [_child] when rule = "INS" ->
      (* INS contradiction case: find ¬P hypothesis and matching P,
         emit refine hN hK (modus ponens on the contradiction) *)
      let resolved = match ctx.entries with
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
      in
      begin match resolved with
      | Some (neg_name, pos_name) ->
        Buffer.add_string buf first_pad;
        Buffer.add_string buf "refine ";
        Buffer.add_string buf neg_name;
        Buffer.add_char buf ' ';
        Buffer.add_string buf pos_name
      | None ->
        Printf.eprintf "warning: INS could not resolve contradiction\n";
        Buffer.add_string buf first_pad;
        Buffer.add_string buf "admit"
      end

    | [child] ->
      (* Generic single child *)
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf eff_rule;
      emit_rule_args buf ctx eff_rule node;
      Buffer.add_string buf " _";
      let ctx' = introduce buf pad ctx rule goal flat in
      let child_flat = compute_child_flat rule flat in
      Buffer.add_string buf ";\n";
      emit_node buf thm_hyps ctx' indent ~flat:child_flat child

    | [child1; child2] when Proof_tree.is_branching_quantifier rule ->
      (* ALL7/XST8 with two children *)
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf eff_rule;
      emit_rule_args buf ctx eff_rule node;
      Buffer.add_string buf " _ _\n";
      Buffer.add_string buf pad;
      Buffer.add_string buf "{ ";
      (* Introduce bound vars in first child *)
      let bvars = binding_vars goal in
      let bvars =
        (* 1-var variants only assume first var from compound binding *)
        if (eff_rule = "ALL7" || eff_rule = "XST8")
           && List.length bvars > 1
        then (match bvars with x :: _ -> [x] | [] -> [])
        else bvars
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
      (* Generic two children *)
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
  pp_prd buf goal;
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
