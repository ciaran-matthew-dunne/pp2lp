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

(* ---- Precedence-aware pretty-printing ----

   Lambdapi precedences (higher = tighter binding):
     ¬     prefix 35       =,≠   infix 10 (no assoc)
     ∧     infix right 7   —     prefix 7
     ∨     infix right 6   +,-   infix left 6    ↦  infix right 6
     ⇒,⇔   infix right 5   ϵ,≤,≪ infix 5 (no assoc)

   Key traps:  = (10) binds TIGHTER than + (6), so a + b = c ≠ (a+b) = c.
               ∧,∨ are RIGHT-assoc in LP — left-assoc chains need explicit parens.

   min_bp = minimum binding power the context requires.  Default 100 (= always
   parenthesise) so every external call site keeps its current behaviour.
   Internal recursive calls pass the real threshold to drop redundant parens. *)

let bp_max = 100 (* atoms, parenthesised groups — never need outer parens *)

let wrap buf need f =
  if need then Buffer.add_char buf '(';
  f ();
  if need then Buffer.add_char buf ')'

(* ---- Expression pretty-printing (shallow encoding) ---- *)

let rec pp_exp ?(min_bp = bp_max) buf e =
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
  | AOp (Add, e1, e2) ->           (* infix left 6 *)
    wrap buf (6 < min_bp) (fun () ->
      pp_exp ~min_bp:6 buf e1;
      Buffer.add_string buf " + ";
      pp_exp ~min_bp:7 buf e2)
  | AOp (Sub, e1, e2) ->           (* infix left 6 *)
    wrap buf (6 < min_bp) (fun () ->
      pp_exp ~min_bp:6 buf e1;
      Buffer.add_string buf " - ";
      pp_exp ~min_bp:7 buf e2)
  | Neg e1 ->                      (* prefix 7 *)
    wrap buf (7 < min_bp) (fun () ->
      Buffer.add_string buf "\xe2\x80\x94 "; (* — *)
      pp_exp ~min_bp:8 buf e1)
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

(* Left-associative conjunction: ((c₀ ∧ c₁) ∧ c₂) ∧ … ∧ cₙ₋₁
   Inner parens enforce left-assoc (essential — LP's ∧ is right-assoc).
   Outer parens are conditional on the surrounding context. *)
let rec pp_conj_left ?(min_bp = bp_max) buf elts =
  match elts with
  | [] -> Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | [p] -> pp_prd ~min_bp buf p
  | first :: rest ->
    let need_outer = 7 < min_bp in
    let n = List.length rest in
    let n_open = n - 1 + (if need_outer then 1 else 0) in
    for _ = 1 to n_open do Buffer.add_char buf '(' done;
    pp_prd ~min_bp:8 buf first;    (* left child of right-assoc ∧ *)
    let closes_left = ref n_open in
    List.iter (fun p ->
      Buffer.add_string buf " \xe2\x88\xa7 "; (* ∧ *)
      pp_prd ~min_bp:8 buf p;      (* each conjunct *)
      if !closes_left > 0 then begin
        Buffer.add_char buf ')';
        decr closes_left
      end
    ) rest

(* ---- Predicate pretty-printing (shallow encoding) ---- *)

and pp_prd ?(min_bp = bp_max) buf p =
  match p with
  | Lift (Var "VRAI") | Lift (Var "TRUE") ->
    Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | Lift (Var "FAUX") | Lift (Var "FALSE") ->
    Buffer.add_string buf "\xe2\x8a\xa5" (* ⊥ *)
  | Lift (App (f, args)) ->         (* ϵ — infix 5 no assoc *)
    wrap buf (5 < min_bp) (fun () ->
      pp_exp_args buf args;
      Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
      pp_ident buf f)
  | Lift (Var s) ->
    pp_ident buf s
  | Lift e ->
    pp_exp ~min_bp buf e
  | Unary (Not, p1) ->              (* prefix 35 *)
    wrap buf (35 < min_bp) (fun () ->
      Buffer.add_string buf "\xc2\xac "; (* ¬ *)
      pp_prd ~min_bp:36 buf p1)
  | Binary (And, _, _) ->           (* infix right 7 *)
    let elts = flatten_conj p in
    pp_conj_left ~min_bp buf elts
  | Binary (Or, p1, p2) ->          (* infix right 6 *)
    wrap buf (6 < min_bp) (fun () ->
      pp_prd ~min_bp:7 buf p1;
      Buffer.add_string buf " \xe2\x88\xa8 "; (* ∨ *)
      pp_prd ~min_bp:6 buf p2)
  | Binary (Imp, p1, p2) ->         (* infix right 5 *)
    wrap buf (5 < min_bp) (fun () ->
      pp_prd ~min_bp:6 buf p1;
      Buffer.add_string buf " \xe2\x87\x92 "; (* ⇒ *)
      pp_prd ~min_bp:5 buf p2)
  | Binary (Iff, p1, p2) ->         (* infix right 5 *)
    wrap buf (5 < min_bp) (fun () ->
      pp_prd ~min_bp:6 buf p1;
      Buffer.add_string buf " \xe2\x87\x94 "; (* ⇔ *)
      pp_prd ~min_bp:5 buf p2)
  | Eq (e1, e2) ->                  (* infix 10 no assoc *)
    wrap buf (10 < min_bp) (fun () ->
      pp_exp ~min_bp:11 buf e1;
      Buffer.add_string buf " = ";
      pp_exp ~min_bp:11 buf e2)
  | Leq (e1, e2) ->                 (* infix 5 no assoc *)
    wrap buf (5 < min_bp) (fun () ->
      pp_exp ~min_bp:6 buf e1;
      Buffer.add_string buf " \xe2\x89\xa4 "; (* ≤ *)
      pp_exp ~min_bp:6 buf e2)
  | Mem (es, e) ->                   (* ϵ — infix 5 no assoc *)
    wrap buf (5 < min_bp) (fun () ->
      pp_exp_args buf es;
      Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
      pp_exp ~min_bp:6 buf e)
  | Bind (binder, xs, body) ->
    let qsym = match binder with
      | Forall0 -> "`\xe2\x88\x80" (* `∀ *)
      | Forall1 -> "`\xe2\x99\xa2"  (* `♢ *)
      | Forall2 -> "`\xe2\x99\xa1"  (* `♡ *)
      | Exists   -> "`\xe2\x88\x83"  (* `∃ *)
    in
    (* Quantifier body extends rightward — always parenthesise for safety *)
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

(* ---- Block-formatted predicate printing ----
   Like pp_prd but inserts line breaks at structural points (⇒, ∧, ∨).
   Used only for the theorem-header goal — proof terms stay compact. *)

let rec pp_prd_block ?(min_bp = 0) ind buf p =
  let pad = String.make ind ' ' in
  match p with
  | Binary (Imp, p1, p2) ->         (* infix right 5 *)
    wrap buf (5 < min_bp) (fun () ->
      pp_prd_block ~min_bp:6 ind buf p1;
      Buffer.add_char buf '\n';
      Buffer.add_string buf pad;
      Buffer.add_string buf "\xe2\x87\x92 "; (* ⇒ *)
      pp_prd_block ~min_bp:5 ind buf p2)
  | Binary (And, _, _) ->           (* infix right 7 *)
    let elts = flatten_conj p in
    pp_conj_left_block ~min_bp ind buf elts
  | Binary (Or, p1, p2) ->          (* infix right 6 *)
    wrap buf (6 < min_bp) (fun () ->
      pp_prd_block ~min_bp:7 ind buf p1;
      Buffer.add_char buf '\n';
      Buffer.add_string buf pad;
      Buffer.add_string buf "\xe2\x88\xa8 "; (* ∨ *)
      pp_prd_block ~min_bp:6 ind buf p2)
  | Bind (binder, xs, body) ->
    let qsym = match binder with
      | Forall0 -> "`\xe2\x88\x80" (* `∀ *)
      | Forall1 -> "`\xe2\x99\xa2"  (* `♢ *)
      | Forall2 -> "`\xe2\x99\xa1"  (* `♡ *)
      | Exists   -> "`\xe2\x88\x83"  (* `∃ *)
    in
    let rec emit_vars = function
      | [] ->
        Buffer.add_char buf '\n';
        Buffer.add_string buf (String.make (ind + 2) ' ');
        pp_prd_block (ind + 2) buf body
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
  | _ ->
    pp_prd ~min_bp buf p

and pp_conj_left_block ?(min_bp = 0) ind buf elts =
  match elts with
  | [] -> Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | [p] -> pp_prd_block ~min_bp ind buf p
  | first :: rest ->
    let need_outer = 7 < min_bp in
    let pad = String.make ind ' ' in
    let n = List.length rest in
    let n_open = n - 1 + (if need_outer then 1 else 0) in
    for _ = 1 to n_open do Buffer.add_char buf '(' done;
    pp_prd_block ~min_bp:8 ind buf first;
    let closes_left = ref n_open in
    List.iter (fun p ->
      Buffer.add_char buf '\n';
      Buffer.add_string buf pad;
      Buffer.add_string buf "\xe2\x88\xa7 "; (* ∧ *)
      pp_prd ~min_bp:8 buf p;
      if !closes_left > 0 then begin
        Buffer.add_char buf ')';
        decr closes_left
      end
    ) rest

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
  | "NRM8" -> true (* ♢x.∀y.Q = ∀x.∀y.Q in HOAS *)
  | _ -> false

let binding_vars = function
  | Binary (Imp, Bind (_, xs, _), _) -> xs
  | Bind (_, xs, _) -> xs
  | _ -> []

(* Count binding variables in the goal's leading binder position.
   Checks several structural patterns where compound bindings occur. *)
let goal_binding_count goal =
  match goal with
  | Binary (Imp, Bind (_, xs, _), _) -> List.length xs
  | Bind (_, xs, _) -> List.length xs
  | Binary (Imp, Unary (Not, Bind (_, xs, _)), _) -> List.length xs
  | Unary (Not, Bind (_, xs, _)) -> List.length xs
  | _ -> 0

let select_variant rule goal children flat =
  match rule, children with
  (* ALL7/XST8: 2-var compound binding → _2 variant (flat=0 only) *)
  | ("ALL7" | "ALL7_1"), _ when goal_binding_count goal >= 2 && flat = 0 ->
    if rule = "ALL7_1" then "ALL7_1_2" else "ALL7_2"
  | "XST8", _ when goal_binding_count goal >= 2 && flat = 0 ->
    "XST8_2"
  (* XST5/XST6/NRM/ALL5: 2-var compound binding → _2 variant *)
  | ("ALL5" | "XST5" | "XST6" | "XST7"
    | "NRM1" | "NRM3" | "NRM5" | "NRM7" | "NRM12" | "NRM13"
    | "NRM14" | "NRM15" | "NRM19"), _
    when goal_binding_count goal >= 2 ->
    rule ^ "_2"
  | _ -> rule

(* ---- Child flat propagation ---- *)

let compute_child_flat rule flat =
  match rule with
  | "ALL5" | "XST5" | "XST7" -> flat + 1
  | "XST5_2" | "XST7_2" -> 0
  | _ when is_hoas_identity rule -> flat
  | _ -> 0

(* ---- Hypothesis/variable introduction ----
   Emits assume lines for IMP4, ALL9, ALL8 and returns updated context. *)

let introduces_antecedent = function
  | "IMP4" | "IMP4_1" | "AR12" | "AR12_1" | "ALL9" -> true
  | _ -> false

let introduce buf pad ctx rule goal flat =
  (* IMP4, AR12, ALL9: introduce antecedent as hypothesis *)
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
  | "EAXM1", Binary (Imp, Eq (e, f), _) ->
    find_hyp ctx (Unary (Not, Eq (f, e)))
  | "EAXM2", Binary (Imp, Unary (Not, Eq (e, f)), _) ->
    find_hyp ctx (Eq (f, e))
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
(* Right-reassociate ∧: ((a∧b)∧c)∧d → a∧(b∧(c∧d))
   Needed because OR3 in primed context produces right-associated conjunctions. *)
let rec right_assoc_conj = function
  | Binary (And, Binary (And, a, b), c) ->
    right_assoc_conj (Binary (And, a, Binary (And, b, c)))
  | p -> p

let emit_quant_r_args buf rule node =
  match node with
  | Apply { children; _ } ->
    let extract_r child_goal =
      match child_goal with
      | Binary (Imp, Bind ((Forall0|Forall1|Forall2), xs, r_body), _) ->
        if rule = "ALL7_2" || rule = "XST8_2" then
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
          Buffer.add_string buf " : \xcf\x84 \xce\xb9, " (* : τ ι, *)
        ) inner_vars;
        pp_prd buf r_body;
        Buffer.add_char buf ')'
      end else
        pp_prd buf r_body;
      Buffer.add_char buf ')'
    | None -> ()
    end

(* OPR1/OPR2: emit child consequent as PE *)
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

(* AR3: emit simplified result from pipe arg *)
let emit_ar3_args buf node =
  match node with
  | Apply { arg = Some (PipeArg (_a_expr, result_expr)); _ } ->
    Buffer.add_string buf " (";
    pp_exp buf result_expr;
    Buffer.add_string buf ") trust"
  | _ ->
    Printf.eprintf "warning: AR3 missing pipe arg\n";
    Buffer.add_string buf " _ trust"

(* AR4: find F from a Leq hypothesis in context *)
let emit_ar4_args buf ctx _goal =
  (* Goal is (E ≤ 0) ⇒ R. Find F ≤ 0 in context. *)
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
    Printf.eprintf "warning: AR4 could not find F ≤ 0 hypothesis\n";
    Buffer.add_string buf " _ trust \xe2\x8a\xa4\xe1\xb5\xa2" (* ⊤ᵢ *)

(* AR5/AR6: find arithmetic hypothesis in context *)
let emit_ar56_args buf =
  Buffer.add_string buf " trust"

(* AR7/AR8: explicit parameter + two trusted arithmetic premises.
   AR7 takes explicit c (unused in child, provide 𝟎).
   AR8 takes explicit a (appears in child equality, extract from child). *)
let emit_ar78_args buf base (node : proof_node) =
  match base with
  | "AR8" ->
    (* Extract a from child's leading equality: (b = a) ⇒ ... *)
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
      Printf.eprintf "warning: AR8 could not extract a from child equality\n";
      Buffer.add_string buf " _ trust trust"
    end
  | _ -> (* AR7: c is not constrained by child, provide 𝟎 *)
    Buffer.add_string buf " \xf0\x9d\x9f\x8e trust trust" (* 𝟎 *)

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
    let ea = Rule_db.emit_args base in
    match ea with
    (* Shared primed+base handlers *)
    | Some "dynamic:axm8" -> emit_axm8_args buf goal
    | Some "dynamic:and5" -> emit_and5_args buf goal node ~primed
    | Some "dynamic:ar9" ->
      (* AR9/AR9_1: emit solver result F from rule arg, then trust for E=F *)
      begin match arg with
      | Some (Pred p) ->
        Buffer.add_string buf " (";
        pp_prd buf p;
        Buffer.add_string buf ") trust"
      | _ ->
        Printf.eprintf "warning: AR9 missing solver arg\n";
        Buffer.add_string buf " _ trust"
      end
    | Some "dynamic:opr1" -> emit_opr_args buf node
    | Some "dynamic:opr2" -> emit_opr_args buf node
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
    | Some "dynamic:ar3" -> emit_ar3_args buf node
    | Some "dynamic:ar4" -> emit_ar4_args buf ctx goal
    | Some "dynamic:ar56" -> emit_ar56_args buf
    | Some "dynamic:ar78" -> emit_ar78_args buf base node
    | Some "dynamic:nrm19" -> emit_nrm19_args buf ctx goal
    (* Static args from JSON *)
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
      Bind (Forall0, vars, compute_result child)
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
        let result_prd = extract_fin_result node primed_child in
        Buffer.add_string buf "refine ALL7_1 (\xce\xbb"; (* λ *)
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
