open Syntax_pp

(* How a PP variable bound by an enclosing compound (n-ary) binder renders:
   [Proj (k, v)] projects slot k from the tuple variable v, printed with the
   infix `v ⋕ k`.  Both goal statements and proof terms use it (the binder var
   is the assumed `Tuple n`).  Defined here because [Pp_lp] is the rendering
   layer [Lp_tree] builds on; re-exported there as [Lp_tree.proj_binding]. *)
type proj_binding =
  | Proj of int * string
type proj_env = (string * proj_binding) list

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

(* Non-negative integer literal as `(from_int <decimal>)`: the file is ℤ-global,
   so the decimal is a `Stdlib.Z.ℤ` and Stdlib.Z computes on it, keeping big apero
   literals (2³¹/2⁶⁴) a single decimal.  `Lit "0"`/`Lit "1"` keep the `𝟎`/`𝟏` abbreviations. *)
let pp_from_int buf decimal =
  Buffer.add_string buf "(from_int ";
  Buffer.add_string buf decimal;
  Buffer.add_char buf ')'

(* Tuple arity / prj index: ℕ-valued.  The file is ℤ-global, so emit the bare
   decimal — the `coerce ℤ ℕ ↪ to_nat` rule (B.lp) inserts the conversion to the
   ℕ index `prj`/`Tuple` expect, so no explicit `to_nat` wrapper is needed. *)
let pp_idx buf k =
  Buffer.add_string buf (string_of_int k)

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

(* PP freshening produces names like `x$0`; render them as the simple ident
   `x0` (drop the `$`).  Anything still non-simple goes through [pp_ident]'s
   `{|…|}` escape, so this only ever improves readability. *)
let sanitize_var s = String.concat "" (String.split_on_char '$' s)

(* Shared header for an n-ary `Bind`: the quantifier symbol, the arity, the LP
   tuple-variable name, the `(slot, let-name)` destructurings to emit, and the
   body env aliasing each PP var to its `let` name.  Both the inline ([pp_prd])
   and block ([pp_prd_block]) printers wrap `(<qsym> <v_name> : Tuple <n>, let
   x0 ≔ (prj 0 v_name) in … <body>)` around this (via [pp_lets]) so the body
   reads with plain names instead of `prj`.  A `let` is emitted only for a var
   the body uses; the env aliases all of them (an unused alias is never looked
   up).  If two vars would sanitize to the same name we keep the exact PP names
   — still pairwise distinct — so no `let` shadows another. *)
let binder_header binder xs env =
  let qsym = match binder with
    | Bang    -> "`!!"
    | Forall  -> "`\xe2\x99\xa2" (* `♢ *)
    | Forall2 -> "`\xe2\x99\xa1" (* `♡ *)
    | Exists  -> "`??"
  in
  let n = List.length xs in
  let sanitized = List.map sanitize_var xs in
  let distinct l = List.length (List.sort_uniq compare l) = List.length l in
  let lp_names = if distinct sanitized then sanitized else xs in
  let v_name = match lp_names with x :: _ -> x ^ "_t" | [] -> "v" in
  (* each bound var renders inline as `v_name ⋕ k`; no `let`-destructuring (which
     blows up lambdapi's checking when the body is a long ⋀ peeled by AND3). *)
  let env' = List.mapi (fun k x -> (x, Proj (k, v_name))) xs @ env in
  (qsym, n, v_name, env')

(* ---- Expression pretty-printing (shallow encoding) ----

   `env` maps a PP variable bound by an enclosing compound binder to how it
   renders: [Proj (k, v)] → the infix `(v ⋕ k)` (slot k of tuple var v).
   Compound binders `Bind (_, xs, body)` are rendered as
   `(\`!! v : Tuple n, … body)` with each `xs.(k)` [Proj]ected to `v ⋕ k` inline
   throughout the body (and likewise in proof terms, where the binder var is
   `assume`d directly as the tuple).  Inner binders shadow outer bindings. *)

let rec pp_exp ?(min_bp = bp_max) ?(env = []) buf e =
  (* B-integer operators print as self-parenthesising prefix applications, so
     min_bp is no longer threaded here; kept for the API. *)
  let _ = min_bp in
  match e with
  | Var s when List.mem_assoc s env ->
    (match List.assoc s env with
     | Proj (k, v) ->
       Buffer.add_char buf '(';
       pp_ident buf v;
       Buffer.add_string buf " \xe2\x8b\x95 "; (* ⋕ *)
       pp_idx buf k;
       Buffer.add_char buf ')')
  | Var "VRAI" | Var "TRUE" -> Buffer.add_string buf "BTRUE"
  | Var "FAUX" | Var "FALSE" -> Buffer.add_string buf "BFALSE"
  | Var s -> pp_ident buf s
  | Lit "0" -> Buffer.add_string buf "\xf0\x9d\x9f\x8e" (* 𝟎 ≔ from_int 0 *)
  | Lit "1" -> Buffer.add_string buf "\xf0\x9d\x9f\x8f" (* 𝟏 ≔ from_int 1 *)
  | Lit s -> pp_from_int buf s                         (* else from_int <decimal> (incl. apero 2⁶⁴ bound) *)
  | App (f, args) ->
    (* PP writes some primitives `_`-prefixed; map to the B.lp names (mirrors
       the `_eql_set` → `eql_set` case). *)
    let f = match f with
      | "_pj1" -> "pj1" | "_pj2" -> "pj2"
      | "_sz" -> "sz" | "_func" -> "func" | s -> s in
    if List.mem f meta_ops then
      (* A B built-in operator: applied directly, not via eapp (see meta_ops). *)
      pp_setop ~env buf f args
    else begin
      Buffer.add_string buf "(eapp ";
      pp_ident buf f;
      Buffer.add_char buf ' ';
      pp_exp_args ~env buf args;
      Buffer.add_char buf ')'
    end
  | EApp (f, args) ->
    Buffer.add_string buf "(eapp ";
    pp_exp ~env buf f;
    Buffer.add_char buf ' ';
    pp_exp_args ~env buf args;
    Buffer.add_char buf ')'
  (* B-integer operators are the prefix symbols `plus`/`minus`/`neg` (B.lp), not
     infix (that would clash with Stdlib.Z's `+`/`-`/`—`), so emit plain
     self-parenthesising applications; operands print at `bp_max`. *)
  | AOp (Add, e1, e2) ->
    Buffer.add_string buf "(plus ";
    pp_exp ~env buf e1; Buffer.add_char buf ' '; pp_exp ~env buf e2;
    Buffer.add_char buf ')'
  | AOp (Sub, e1, e2) ->
    Buffer.add_string buf "(minus ";
    pp_exp ~env buf e1; Buffer.add_char buf ' '; pp_exp ~env buf e2;
    Buffer.add_char buf ')'
  | Neg e1 ->
    Buffer.add_string buf "(neg ";
    pp_exp ~env buf e1;
    Buffer.add_char buf ')'
  (* Set-theoretic operators are higher-order symbols (e.g. inter :
     τι→τι→τι), applied DIRECTLY — `eapp` is only for B-function (set-of-pairs)
     application (the App/EApp cases above). *)
  | SetImage (e1, e2) -> pp_setop ~env buf "set_image" [e1; e2]
  | Inter (e1, e2) -> pp_setop ~env buf "inter" [e1; e2]
  | Union (e1, e2) -> pp_setop ~env buf "union" [e1; e2]
  | Range (e1, e2) -> pp_setop ~env buf "interval" [e1; e2]
  | Inverse e -> pp_setop ~env buf "inverse" [e]
  | DomRestrict (e1, e2) -> pp_setop ~env buf "dom_restrict" [e1; e2]
  | RanRestrict (e1, e2) -> pp_setop ~env buf "ran_restrict" [e1; e2]
  | SetOp (name, args) -> pp_setop ~env buf name args
  | BoolOf pred ->              (* bool(P) ↦ (bool_of P) *)
    Buffer.add_string buf "(bool_of ";
    pp_prd ~env buf pred;
    Buffer.add_char buf ')'
  | Maplet (e1, e2) ->          (* genuine ordered pair — the ↦ constructor *)
    Buffer.add_string buf "(";
    pp_exp ~env buf e1;
    Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
    pp_exp ~env buf e2;
    Buffer.add_string buf ")"
  | SetLit es ->
    (* {a,b,c} ↦ right-fold of `set_cons a (… set_empty)` *)
    let rec fold = function
      | [] -> Buffer.add_string buf "set_empty"
      | e :: rest ->
        Buffer.add_string buf "(set_cons ";
        pp_exp ~env buf e;
        Buffer.add_char buf ' ';
        fold rest;
        Buffer.add_char buf ')'
    in
    fold es
  | Compr (op, xs, pred, value) ->
    (* %(xs).(P|E) / SIGMA(xs).(P|E) ↦ (<op> (λ v, P) (λ v, E)); the bound vars
       project from one `Tuple n` LP variable, like the quantifier kernels. *)
    let n = List.length xs in
    let v_name = match xs with x :: _ -> x ^ "_t" | [] -> "v" in
    (* Comprehensions keep inline `prj` (no `let`-destructuring) — they wrap two
       λ-bodies sharing one tuple var, where `let`s would clutter more than help,
       and they barely occur in the type-checked suites. *)
    let env' = List.mapi (fun k x -> (x, Proj (k, v_name))) xs @ env in
    let lam tail =
      Buffer.add_string buf "(\xce\xbb "; (* λ *)
      pp_ident buf v_name;
      Buffer.add_string buf " : Tuple ";
      pp_idx buf n;
      Buffer.add_string buf ", ";
      tail ();
      Buffer.add_char buf ')'
    in
    Buffer.add_char buf '(';
    Buffer.add_string buf op;
    Buffer.add_char buf ' ';
    lam (fun () -> pp_prd ~env:env' buf pred);
    Buffer.add_char buf ' ';
    lam (fun () -> pp_exp ~env:env' buf value);
    Buffer.add_char buf ')'

(* A higher-order set operator applied directly: `(name a b …)`, each argument
   fully parenthesised (default min_bp). *)
and pp_setop ?(env = []) buf name args =
  (* `prod` with an integer-literal operand is arithmetic `k·x` (a literal can't be
     a Cartesian operand), so render it as the arithmetic `mult`; a genuine set
     product (no literal) stays `prod`.  Keeps B.lp's `mult`/`prod` distinct. *)
  let name = match name, args with
    | "prod", ([ Lit _; _ ] | [ _; Lit _ ]) -> "mult"
    | _ -> name in
  Buffer.add_char buf '(';
  Buffer.add_string buf name;
  List.iter (fun a -> Buffer.add_char buf ' '; pp_exp ~env buf a) args;
  Buffer.add_char buf ')'

and pp_exp_args ?(env = []) buf = function
  | [e] -> pp_exp ~env buf e
  | e :: rest ->
    Buffer.add_char buf '(';
    pp_exp ~env buf e;
    List.iter (fun e' ->
      Buffer.add_string buf " \xe2\x86\xa6 "; (* ↦ *)
      pp_exp ~env buf e') rest;
    Buffer.add_char buf ')'
  | [] -> failwith "pp_exp_args: empty argument list (malformed App/Mem)"

(* ---- Predicate pretty-printing (shallow encoding) ---- *)

and pp_prd ?(min_bp = bp_max) ?(env = []) buf p =
  match p with
  | Lift (Var "VRAI") | Lift (Var "TRUE") ->
    Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | Lift (Var "FAUX") | Lift (Var "FALSE") ->
    Buffer.add_string buf "\xe2\x8a\xa5" (* ⊥ *)
  | Lift (App (f, args)) ->
    if f = "_eql_set" || f = "eql_set" then
      match args with
      | [e1; e2] ->
        wrap buf (5 < min_bp) (fun () ->
          Buffer.add_string buf "eql_set ";
          pp_exp ~min_bp:6 ~env buf e1;
          Buffer.add_char buf ' ';
          pp_exp ~min_bp:6 ~env buf e2)
      | _ -> failwith "pp_lp: eql_set must have exactly 2 arguments"
    else if f = "_func" || f = "func" then
      (* _func(f, dom, ran): the 3-ary function-hood predicate (B.lp `func`,
         Prop-valued), a direct application — NOT a membership like the generic
         relational `r(a,…) = (a,…) ϵ r` case below. *)
      (match args with
       | [e1; e2; e3] ->
         wrap buf (5 < min_bp) (fun () ->
           Buffer.add_string buf "func ";
           pp_exp ~min_bp:6 ~env buf e1; Buffer.add_char buf ' ';
           pp_exp ~min_bp:6 ~env buf e2; Buffer.add_char buf ' ';
           pp_exp ~min_bp:6 ~env buf e3)
       | _ -> failwith "pp_lp: _func must have exactly 3 arguments")
    else
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
  | Unary (Instanciation, p1) ->
    (* __INSTANCIATION(P) is logically P — emit transparently. *)
    pp_prd ~min_bp ~env buf p1
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
  | Leq (e1, e2) ->                       (* `leq` is the prefix B-integer ≤ (B.lp) *)
    Buffer.add_string buf "(leq ";
    pp_exp ~env buf e1; Buffer.add_char buf ' '; pp_exp ~env buf e2;
    Buffer.add_char buf ')'
  | Mem (es, e) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_exp_args ~env buf es;
      Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
      pp_exp ~min_bp:6 ~env buf e)
  | Rel (name, args) ->         (* uninterpreted Prop operator, applied directly *)
    pp_setop ~env buf name args
  | Bind (binder, xs, body) ->
    let qsym, n, v_name, env' = binder_header binder xs env in
    Buffer.add_char buf '(';
    Buffer.add_string buf qsym;
    Buffer.add_char buf ' ';
    pp_ident buf v_name;
    Buffer.add_string buf " : Tuple ";
    pp_idx buf n;
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
    Buffer.add_string buf "\xe2\x8b\x80 (\xe2\x88\x8e"; (* ⋀ (∎ *)
    List.iter (fun p ->
      Buffer.add_string buf " \xe2\x88\xb7 "; (* ∷ *)
      pp_prd ~min_bp:21 ~env buf p;
    ) elts;
    Buffer.add_char buf ')';
    if need_wrap then Buffer.add_char buf ')'

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
    let qsym, n, v_name, env' = binder_header binder xs env in
    Buffer.add_char buf '(';
    Buffer.add_string buf qsym;
    Buffer.add_char buf ' ';
    pp_ident buf v_name;
    Buffer.add_string buf " : Tuple ";
    pp_idx buf n;
    Buffer.add_char buf ',';
    Buffer.add_char buf '\n';
    let inner_pad = String.make (ind + 2) ' ' in
    Buffer.add_string buf inner_pad;
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
    Buffer.add_string buf "\xe2\x8b\x80 (\xe2\x88\x8e"; (* ⋀ (∎ *)
    List.iter (fun p ->
      Buffer.add_char buf '\n';
      Buffer.add_string buf pad;
      Buffer.add_string buf " \xe2\x88\xb7 "; (* ∷ *)
      pp_prd_block ~min_bp:21 ~env (ind + 4) buf p;
    ) elts;
    Buffer.add_char buf ')';
    if need_wrap then Buffer.add_char buf ')'
  end
