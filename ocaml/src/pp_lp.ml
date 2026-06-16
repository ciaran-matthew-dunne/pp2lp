open Syntax_pp

(* How a PP variable bound by an enclosing compound (n-ary) binder renders.
   See [Lp_tree.proj_binding] for the full contract — [Proj] projects from a
   tuple (proof context), [Alias] names a `let`-bound destructuring (goal
   statement).  Defined here because [Pp_lp] is the rendering layer [Lp_tree]
   builds on; re-exported there as [Lp_tree.proj_binding]. *)
type proj_binding =
  | Proj of int * string
  | Alias of string
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

(* Write `(from_int (Stdlib.Z.Zpos P))` for a positive decimal literal, P the
   binary Stdlib.Pos built MSB→LSB from [pos_bits].  ℤ literals are written
   explicitly because bench bare numerals are ℕ (Tuple arities); the binary
   form keeps apero's 2³¹/2⁶⁴ literals compact (no unary 𝟏-sum blowup). *)
let pp_from_int_pos buf decimal =
  Buffer.add_string buf "(from_int (Stdlib.Z.Zpos ";
  (match Syntax_pp.pos_bits decimal with
   | [] -> Buffer.add_string buf "Stdlib.Pos.H"   (* unreachable: decimal ≥ 2 *)
   | _ :: rest ->
     (* `O p = 2p`, `I p = 2p+1` ⇒ outermost constructor is the LSB, so wrap
        from the least-significant `rest` bit (last) outward to H (the MSB). *)
     let lsb_first = List.rev rest in
     List.iter (fun b ->
       Buffer.add_string buf
         (if b = 1 then "(Stdlib.Pos.I " else "(Stdlib.Pos.O ")) lsb_first;
     Buffer.add_string buf "Stdlib.Pos.H";
     List.iter (fun _ -> Buffer.add_char buf ')') lsb_first);
  Buffer.add_string buf "))"

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

(* Does PP variable [x] occur in [body], not captured by an inner binder?  Used
   to drop the `let` for a bound var the body never mentions (so no useless
   `let`-binding is emitted).  Deliberately raw — it counts every `Var x`, so
   (unlike [Free_vars], which filters library names) it never reports a
   referenced var as absent just because it shares a B.lp global's name (a bound
   `id`, `seq`, …), which would drop a needed `let` and leave it unbound. *)
let rec occurs_exp x = function
  | Var s -> s = x
  | Compr (_, ys, pred, value) ->
    not (List.mem x ys) && (occurs_prd x pred || occurs_exp x value)
  | BoolOf pred -> occurs_prd x pred
  | e -> fold_exp (fun acc e' -> acc || occurs_exp x e') false e
and occurs_prd x = function
  | Bind (_, ys, body) -> not (List.mem x ys) && occurs_prd x body
  | Lift e -> occurs_exp x e
  | Unary (_, p) -> occurs_prd x p
  | Binary (_, p1, p2) -> occurs_prd x p1 || occurs_prd x p2
  | Eq (e1, e2) | Leq (e1, e2) -> occurs_exp x e1 || occurs_exp x e2
  | Mem (es, e) -> List.exists (occurs_exp x) es || occurs_exp x e
  | Rel (_, es) -> List.exists (occurs_exp x) es

(* Shared header for an n-ary `Bind`: the quantifier symbol, the arity, the LP
   tuple-variable name, the `(slot, let-name)` destructurings to emit, and the
   body env aliasing each PP var to its `let` name.  Both the inline ([pp_prd])
   and block ([pp_prd_block]) printers wrap `(<qsym> <v_name> : Tuple <n>, let
   x0 ≔ (prj 0 v_name) in … <body>)` around this (via [pp_lets]) so the body
   reads with plain names instead of `prj`.  A `let` is emitted only for a var
   the body uses; the env aliases all of them (an unused alias is never looked
   up).  If two vars would sanitize to the same name we keep the exact PP names
   — still pairwise distinct — so no `let` shadows another. *)
let binder_header binder xs body env =
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
  let env' = List.map2 (fun x lp -> (x, Alias lp)) xs lp_names @ env in
  let lets =
    List.filteri (fun k _ -> occurs_prd (List.nth xs k) body)
      (List.mapi (fun k lp -> (k, lp)) lp_names) in
  (qsym, n, v_name, lets, env')

(* Emit the `let <name> ≔ (prj k <v_name>) in` destructuring lines that open a
   compound binder's body.  [lets] is the kept `(slot, name)` pairs.  [sep] is
   run after each `in` — a single space inline, a newline + indent in block. *)
let pp_lets buf ~sep v_name lets =
  List.iter (fun (k, name) ->
    Buffer.add_string buf "let ";
    pp_ident buf name;
    Buffer.add_string buf " \xe2\x89\x94 (prj "; (* ≔ (prj *)
    Buffer.add_string buf (string_of_int k);
    Buffer.add_char buf ' ';
    pp_ident buf v_name;
    Buffer.add_string buf ") in";
    sep ()) lets

(* ---- Expression pretty-printing (shallow encoding) ----

   `env` maps a PP variable bound by an enclosing compound binder to how it
   renders: [Proj (k, v)] → `(prj k v)`, or [Alias name] → the bare identifier
   `name`.  Compound binders `Bind (_, xs, body)` are rendered as
   `(\`!! v : Tuple n, let x0 ≔ (prj 0 v) in … body)`: the body opens with one
   `let` per bound var (so it reads with plain names), and each `xs.(k)` is
   [Alias]ed to its `let` name in `env`.  In a *proof* term, by contrast, the
   binder var is `assume`d directly as the tuple, so its env uses [Proj] and the
   vars render as `prj k v`.  Inner binders shadow outer bindings. *)

let rec pp_exp ?(min_bp = bp_max) ?(env = []) buf e =
  match e with
  | Var s when List.mem_assoc s env ->
    (match List.assoc s env with
     | Proj (k, v) ->
       Buffer.add_string buf "(prj ";
       Buffer.add_string buf (string_of_int k);
       Buffer.add_char buf ' ';
       pp_ident buf v;
       Buffer.add_char buf ')'
     | Alias name -> pp_ident buf name)
  | Var "VRAI" | Var "TRUE" -> Buffer.add_string buf "BTRUE"
  | Var "FAUX" | Var "FALSE" -> Buffer.add_string buf "BFALSE"
  | Var s -> pp_ident buf s
  | BigNat s -> pp_from_int_pos buf s
  | Nat 0 -> Buffer.add_string buf "\xf0\x9d\x9f\x8e" (* 𝟎 ≔ from_int 0 *)
  | Nat 1 -> Buffer.add_string buf "\xf0\x9d\x9f\x8f" (* 𝟏 ≔ from_int 1 *)
  | Nat n -> pp_from_int_pos buf (string_of_int n)   (* n ≥ 2 → from_int binary ℤ *)
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
      Buffer.add_string buf (string_of_int n);
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
  | Rel (name, args) ->         (* uninterpreted Prop operator, applied directly *)
    pp_setop ~env buf name args
  | Bind (binder, xs, body) ->
    let qsym, n, v_name, lets, env' = binder_header binder xs body env in
    Buffer.add_char buf '(';
    Buffer.add_string buf qsym;
    Buffer.add_char buf ' ';
    pp_ident buf v_name;
    Buffer.add_string buf " : Tuple ";
    Buffer.add_string buf (string_of_int n);
    Buffer.add_string buf ", ";
    pp_lets buf ~sep:(fun () -> Buffer.add_char buf ' ') v_name lets;
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
    let qsym, n, v_name, lets, env' = binder_header binder xs body env in
    Buffer.add_char buf '(';
    Buffer.add_string buf qsym;
    Buffer.add_char buf ' ';
    pp_ident buf v_name;
    Buffer.add_string buf " : Tuple ";
    Buffer.add_string buf (string_of_int n);
    Buffer.add_char buf ',';
    Buffer.add_char buf '\n';
    let inner_pad = String.make (ind + 2) ' ' in
    Buffer.add_string buf inner_pad;
    pp_lets buf
      ~sep:(fun () -> Buffer.add_char buf '\n'; Buffer.add_string buf inner_pad)
      v_name lets;
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
