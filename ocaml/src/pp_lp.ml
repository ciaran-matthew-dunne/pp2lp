open Syntax_pp

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

let bp_max = 100

let wrap buf need f =
  if need then Buffer.add_char buf '(';
  f ();
  if need then Buffer.add_char buf ')'

(* ---- Expression pretty-printing (shallow encoding) ----

   `env` maps PP variable names bound by an enclosing compound binder to
   their tuple-projection rendering `(k, v)` — emitted as `(prj k v)`.
   Compound binders `Bind (_, xs, body)` are rendered as
   `(\`!! v : Tuple n, body)` with each `xs.(k)` substituted by
   `prj k v` at emission time, matching the n-ary quantifier kernel
   exposed by `lp/Quant.lp`. Inner binders shadow outer bindings. *)

let rec pp_exp ?(min_bp = bp_max) ?(env = []) buf e =
  match e with
  | Var s when List.mem_assoc s env ->
    let (k, v) = List.assoc s env in
    Buffer.add_string buf "(prj ";
    Buffer.add_string buf (string_of_int k);
    Buffer.add_char buf ' ';
    pp_ident buf v;
    Buffer.add_char buf ')'
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
    pp_exp_args ~env buf args;
    Buffer.add_char buf ')'
  | AOp (Add, e1, e2) ->
    wrap buf (6 < min_bp) (fun () ->
      pp_exp ~min_bp:6 ~env buf e1;
      Buffer.add_string buf " + ";
      pp_exp ~min_bp:7 ~env buf e2)
  | AOp (Sub, e1, e2) ->
    wrap buf (6 < min_bp) (fun () ->
      pp_exp ~min_bp:6 ~env buf e1;
      Buffer.add_string buf " - ";
      pp_exp ~min_bp:7 ~env buf e2)
  | Neg e1 ->
    wrap buf (7 < min_bp) (fun () ->
      Buffer.add_string buf "\xe2\x80\x94 "; (* — *)
      pp_exp ~min_bp:8 ~env buf e1)
  | SetImage (e1, e2) ->
    Buffer.add_string buf "(eapp set_image (";
    pp_exp ~env buf e1;
    Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
    pp_exp ~env buf e2;
    Buffer.add_string buf "))"
  | Inter (e1, e2) ->
    Buffer.add_string buf "(eapp inter (";
    pp_exp ~env buf e1;
    Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
    pp_exp ~env buf e2;
    Buffer.add_string buf "))"
  | Union (e1, e2) ->
    Buffer.add_string buf "(eapp union (";
    pp_exp ~env buf e1;
    Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
    pp_exp ~env buf e2;
    Buffer.add_string buf "))"

and pp_exp_args ?(env = []) buf = function
  | [e] -> pp_exp ~env buf e
  | e :: rest ->
    Buffer.add_char buf '(';
    pp_exp ~env buf e;
    List.iter (fun e' ->
      Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
      pp_exp ~env buf e') rest;
    Buffer.add_char buf ')'
  | [] -> Buffer.add_string buf "\xf0\x9d\x9f\x8e" (* 𝟎 as fallback *)

(* ---- Conjunction helpers ----

   [conj_leaves] walks both children of an And tree, collecting every
   non-∧ leaf regardless of associativity:
     ((a ∧ b) ∧ c)  →  [a; b; c]
     (a ∧ (b ∧ c))  →  [a; b; c]
   Used for: AXM8/AND5 structural matching, INS heart matching,
   `.but` antecedent splitting, and ∧* list emission. *)

let rec conj_leaves = function
  | Binary (And, l, r) -> conj_leaves l @ conj_leaves r
  | p -> [p]

(* [conj_children_left] splits only the left spine of a left-associative
   ∧ tree, preserving right-hand sub-conjunctions as single elements:
     ((a ∧ b) ∧ c)        →  [a; b; c]
     ((a ∧ b) ∧ (c ∧ d))  →  [a; b; (c ∧ d)]
   Matches the ⋀ list structure after AND5 modifications. *)
let rec conj_children_left = function
  | Binary (And, l, r) -> conj_children_left l @ [r]
  | p -> [p]

(* ---- Predicate pretty-printing (shallow encoding) ---- *)

let rec pp_prd ?(min_bp = bp_max) ?(env = []) buf p =
  match p with
  | Lift (Var "VRAI") | Lift (Var "TRUE") ->
    Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | Lift (Var "FAUX") | Lift (Var "FALSE") ->
    Buffer.add_string buf "\xe2\x8a\xa5" (* ⊥ *)
  | Lift (App (f, args)) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_exp_args ~env buf args;
      Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
      pp_ident buf f)
  | Lift (Var s) when List.mem_assoc s env ->
    pp_exp ~min_bp ~env buf (Var s)
  | Lift (Var s) ->
    pp_ident buf s
  | Lift e ->
    pp_exp ~min_bp ~env buf e
  | Unary (Not, p1) ->
    wrap buf (35 < min_bp) (fun () ->
      Buffer.add_string buf "\xc2\xac "; (* ¬ *)
      pp_prd ~min_bp:36 ~env buf p1)
  | Binary (And, _, _) ->
    (* Use [conj_children_left] to preserve right-hand sub-conjunctions
       as nested `⋀` cells: PP treats `a and (b and c)` as a 2-element
       conjunction whose second element is itself a conjunction, and
       its AND4 proof tree mirrors that nesting.  Flattening with
       [conj_leaves] would merge `(b and c)` into the outer list and
       desynchronise the proof tree from the encoded goal. *)
    let elts = conj_children_left p in
    pp_conj_list ~min_bp ~env buf elts
  | Binary (Or, p1, p2) ->
    wrap buf (6 < min_bp) (fun () ->
      pp_prd ~min_bp:7 ~env buf p1;
      Buffer.add_string buf " \xe2\x88\xa8 "; (* ∨ *)
      pp_prd ~min_bp:6 ~env buf p2)
  | Binary (Imp, p1, p2) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_prd ~min_bp:6 ~env buf p1;
      Buffer.add_string buf " \xe2\x87\x92 "; (* ⇒ *)
      pp_prd ~min_bp:5 ~env buf p2)
  | Binary (Iff, p1, p2) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_prd ~min_bp:6 ~env buf p1;
      Buffer.add_string buf " \xe2\x87\x94 "; (* ⇔ *)
      pp_prd ~min_bp:5 ~env buf p2)
  | Eq (e1, e2) ->
    wrap buf (10 < min_bp) (fun () ->
      pp_exp ~min_bp:11 ~env buf e1;
      Buffer.add_string buf " = ";
      pp_exp ~min_bp:11 ~env buf e2)
  | Leq (e1, e2) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_exp ~min_bp:6 ~env buf e1;
      Buffer.add_string buf " \xe2\x89\xa4 "; (* ≤ *)
      pp_exp ~min_bp:6 ~env buf e2)
  | Mem (es, e) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_exp_args ~env buf es;
      Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
      pp_exp ~min_bp:6 ~env buf e)
  | Bind (binder, xs, body) ->
    let qsym = match binder with
      | Bang    -> "`!!"
      | Forall  -> "`\xe2\x99\xa2" (* `♢ *)
      | Forall2 -> "`\xe2\x99\xa1" (* `♡ *)
      | Exists  -> "`??"
    in
    let n = List.length xs in
    let v_name = match xs with x :: _ -> x ^ "_t" | [] -> "v" in
    let env' =
      List.mapi (fun k x -> (x, (k, v_name))) xs @ env
    in
    Buffer.add_char buf '(';
    Buffer.add_string buf qsym;
    Buffer.add_char buf ' ';
    pp_ident buf v_name;
    Buffer.add_string buf " : Tuple ";
    Buffer.add_string buf (string_of_int n);
    Buffer.add_string buf ", ";
    pp_prd ~env:env' buf body;
    Buffer.add_char buf ')'

and pp_conj_list ?(min_bp = bp_max) ?(env = []) buf elts =
  match elts with
  | [] ->
    Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | _ ->
    let need_wrap = 30 < min_bp in
    if need_wrap then Buffer.add_char buf '(';
    Buffer.add_string buf "\xe2\x8b\x80 ("; (* ⋀ ( *)
    List.iter (fun p ->
      pp_prd ~min_bp:21 ~env buf p;
      Buffer.add_string buf " \xe2\xb8\xac "; (* ⸬ *)
    ) elts;
    Buffer.add_string buf "\xe2\x96\xa1)"; (* □) *)
    if need_wrap then Buffer.add_char buf ')'

and pp_conj_tail ?(env = []) buf elts =
  match elts with
  | [] -> Buffer.add_string buf "\xe2\x96\xa1" (* □ *)
  | _ ->
    Buffer.add_char buf '(';
    List.iter (fun p ->
      pp_prd ~min_bp:21 ~env buf p;
      Buffer.add_string buf " \xe2\xb8\xac "; (* ⸬ *)
    ) elts;
    Buffer.add_string buf "\xe2\x96\xa1)" (* □) *)

(* ---- ⋀ extraction/reconstruction ----
   ⋀ (P₀ ⸬ P₁ ⸬ … ⸬ Pₙ₋₁ ⸬ □)
   Element k: k applications of ⋀_tl then ⋀_hd.
   ⋀_hd/⋀_tl take (P : Prop) (rest : 𝕃 o) — passed as _ _. *)

let rec emit_tl_chain buf var k =
  if k = 0 then Buffer.add_string buf var
  else begin
    Buffer.add_string buf "(\xe2\x8b\x80_tl _ _ "; (* (⋀_tl _ _  *)
    emit_tl_chain buf var (k - 1);
    Buffer.add_char buf ')'
  end

let emit_extract buf var _conjs k =
  Buffer.add_string buf "\xe2\x8b\x80_hd _ _ "; (* ⋀_hd _ _  *)
  emit_tl_chain buf var k

let rec emit_conj_from_elts buf (elts : (Buffer.t -> unit) list) =
  match elts with
  | [] ->
    Buffer.add_string buf "\xe2\x8b\x80_nil_prf" (* ⋀_nil_prf *)
  | [e] -> e buf
  | [e1; e2] ->
    (* 2-element base: use ⋀_bin transport to avoid opaque singleton *)
    Buffer.add_string buf "(=\xe2\x87\x92 (eq_sym (\xe2\x8b\x80_bin _ _)) (\xe2\x88\xa7\xe1\xb5\xa2 ";
    (* (=⇒ (eq_sym (⋀_bin _ _)) (∧ᵢ  *)
    e1 buf;
    Buffer.add_char buf ' ';
    e2 buf;
    Buffer.add_string buf "))"
  | e :: rest ->
    (* 3+ elements: ⋀_cons transport, rest is 2+ so ⋀ stays opaque *)
    Buffer.add_string buf "(=\xe2\x87\x92 (eq_sym (\xe2\x8b\x80_cons _ _)) (\xe2\x88\xa7\xe1\xb5\xa2 ";
    (* (=⇒ (eq_sym (⋀_cons _ _)) (∧ᵢ  *)
    e buf;
    Buffer.add_char buf ' ';
    emit_conj_from_elts buf rest;
    Buffer.add_string buf "))"

let emit_and5_fwd buf var conjs ant_positions j =
  let n = List.length conjs in
  let elts = ref [] in
  for k = 0 to n - 1 do
    if k <> j then
      elts := !elts @ [(fun buf ->
        Buffer.add_char buf '(';
        emit_extract buf var conjs k;
        Buffer.add_char buf ')')]
  done;
  let ant_proof buf =
    let ant_extractors = List.map (fun i buf ->
      Buffer.add_char buf '(';
      emit_extract buf var conjs i;
      Buffer.add_char buf ')'
    ) ant_positions in
    emit_conj_from_elts buf ant_extractors
  in
  elts := !elts @ [(fun buf ->
    Buffer.add_string buf "((";
    emit_extract buf var conjs j;
    Buffer.add_string buf ") ";
    ant_proof buf;
    Buffer.add_char buf ')')];
  emit_conj_from_elts buf !elts

(* ---- Block-formatted predicate printing ---- *)

(* Column width threshold: if inline rendering fits, skip line breaks. *)
let block_width = 72

let rec pp_prd_block ?(min_bp = 0) ?(env = []) ind buf p =
  (* Try inline first — if it fits, use it *)
  let inline = Buffer.create 128 in
  pp_prd ~min_bp ~env inline p;
  if Buffer.length inline + ind <= block_width then
    Buffer.add_buffer buf inline
  else
    pp_prd_block_break ~min_bp ~env ind buf p

and pp_prd_block_break ?(min_bp = 0) ?(env = []) ind buf p =
  let pad = String.make ind ' ' in
  match p with
  | Binary (Imp, p1, p2) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_prd_block ~min_bp:6 ~env ind buf p1;
      Buffer.add_char buf '\n';
      Buffer.add_string buf pad;
      Buffer.add_string buf "\xe2\x87\x92 "; (* ⇒ *)
      pp_prd_block ~min_bp:5 ~env ind buf p2)
  | Binary (And, _, _) ->
    (* Mirror the inline branch: preserve right-hand sub-conjunctions
       (`conj_children_left`) so block formatting agrees with the
       proof-tree nesting that PP's AND4 chain expects. *)
    let elts = conj_children_left p in
    pp_conj_list_block ~min_bp ~env ind buf elts
  | Binary (Or, p1, p2) ->
    wrap buf (6 < min_bp) (fun () ->
      pp_prd_block ~min_bp:7 ~env ind buf p1;
      Buffer.add_char buf '\n';
      Buffer.add_string buf pad;
      Buffer.add_string buf "\xe2\x88\xa8 "; (* ∨ *)
      pp_prd_block ~min_bp:6 ~env ind buf p2)
  | Bind (binder, xs, body) ->
    let qsym = match binder with
      | Bang    -> "`!!"
      | Forall  -> "`\xe2\x99\xa2" (* `♢ *)
      | Forall2 -> "`\xe2\x99\xa1" (* `♡ *)
      | Exists  -> "`??"
    in
    let n = List.length xs in
    let v_name = match xs with x :: _ -> x ^ "_t" | [] -> "v" in
    let env' =
      List.mapi (fun k x -> (x, (k, v_name))) xs @ env
    in
    Buffer.add_char buf '(';
    Buffer.add_string buf qsym;
    Buffer.add_char buf ' ';
    pp_ident buf v_name;
    Buffer.add_string buf " : Tuple ";
    Buffer.add_string buf (string_of_int n);
    Buffer.add_char buf ',';
    Buffer.add_char buf '\n';
    Buffer.add_string buf (String.make (ind + 2) ' ');
    pp_prd_block ~env:env' (ind + 2) buf body;
    Buffer.add_char buf ')'
  | _ ->
    pp_prd ~min_bp ~env buf p

and pp_conj_list_block ?(min_bp = 0) ?(env = []) ind buf elts =
  let inline = Buffer.create 128 in
  pp_conj_list ~min_bp ~env inline elts;
  if Buffer.length inline + ind <= block_width then
    Buffer.add_buffer buf inline
  else begin
    let pad = String.make ind ' ' in
    let need_wrap = 30 < min_bp in
    if need_wrap then Buffer.add_char buf '(';
    Buffer.add_string buf "\xe2\x8b\x80 ("; (* ⋀ ( *)
    List.iter (fun p ->
      pp_prd_block ~min_bp:21 ~env (ind + 4) buf p;
      Buffer.add_char buf '\n';
      Buffer.add_string buf pad;
      Buffer.add_string buf " \xe2\xb8\xac "; (* ⸬ *)
    ) elts;
    Buffer.add_string buf "\xe2\x96\xa1)"; (* □) *)
    if need_wrap then Buffer.add_char buf ')'
  end
