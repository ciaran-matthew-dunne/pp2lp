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
  | AOp (Add, e1, e2) ->
    wrap buf (6 < min_bp) (fun () ->
      pp_exp ~min_bp:6 buf e1;
      Buffer.add_string buf " + ";
      pp_exp ~min_bp:7 buf e2)
  | AOp (Sub, e1, e2) ->
    wrap buf (6 < min_bp) (fun () ->
      pp_exp ~min_bp:6 buf e1;
      Buffer.add_string buf " - ";
      pp_exp ~min_bp:7 buf e2)
  | Neg e1 ->
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

let rec pp_conj_left ?(min_bp = bp_max) buf elts =
  match elts with
  | [] -> Buffer.add_string buf "\xe2\x8a\xa4" (* ⊤ *)
  | [p] -> pp_prd ~min_bp buf p
  | first :: rest ->
    let need_outer = 7 < min_bp in
    let n = List.length rest in
    let n_open = n - 1 + (if need_outer then 1 else 0) in
    for _ = 1 to n_open do Buffer.add_char buf '(' done;
    pp_prd ~min_bp:8 buf first;
    let closes_left = ref n_open in
    List.iter (fun p ->
      Buffer.add_string buf " \xe2\x88\xa7 "; (* ∧ *)
      pp_prd ~min_bp:8 buf p;
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
  | Lift (App (f, args)) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_exp_args buf args;
      Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
      pp_ident buf f)
  | Lift (Var s) ->
    pp_ident buf s
  | Lift e ->
    pp_exp ~min_bp buf e
  | Unary (Not, p1) ->
    wrap buf (35 < min_bp) (fun () ->
      Buffer.add_string buf "\xc2\xac "; (* ¬ *)
      pp_prd ~min_bp:36 buf p1)
  | Binary (And, _, _) ->
    let elts = flatten_conj p in
    pp_conj_left ~min_bp buf elts
  | Binary (Or, p1, p2) ->
    wrap buf (6 < min_bp) (fun () ->
      pp_prd ~min_bp:7 buf p1;
      Buffer.add_string buf " \xe2\x88\xa8 "; (* ∨ *)
      pp_prd ~min_bp:6 buf p2)
  | Binary (Imp, p1, p2) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_prd ~min_bp:6 buf p1;
      Buffer.add_string buf " \xe2\x87\x92 "; (* ⇒ *)
      pp_prd ~min_bp:5 buf p2)
  | Binary (Iff, p1, p2) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_prd ~min_bp:6 buf p1;
      Buffer.add_string buf " \xe2\x87\x94 "; (* ⇔ *)
      pp_prd ~min_bp:5 buf p2)
  | Eq (e1, e2) ->
    wrap buf (10 < min_bp) (fun () ->
      pp_exp ~min_bp:11 buf e1;
      Buffer.add_string buf " = ";
      pp_exp ~min_bp:11 buf e2)
  | Leq (e1, e2) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_exp ~min_bp:6 buf e1;
      Buffer.add_string buf " \xe2\x89\xa4 "; (* ≤ *)
      pp_exp ~min_bp:6 buf e2)
  | Mem (es, e) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_exp_args buf es;
      Buffer.add_string buf " \xcf\xb5 "; (* ϵ *)
      pp_exp ~min_bp:6 buf e)
  | Bind (binder, xs, body) ->
    let qsym = match binder with
      | Bang -> "`\xe2\x88\x80"   (* `∀ *)
      | Forall -> "`\xe2\x99\xa2"  (* `♢ *)
      | Forall2 -> "`\xe2\x99\xa1" (* `♡ *)
      | Exists   -> "`\xe2\x88\x83" (* `∃ *)
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

(* ---- Left-associative conjunction extraction/reconstruction ---- *)

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

(* ---- Convenience stringifiers ---- *)

let prd_to_string p =
  let buf = Buffer.create 256 in
  pp_prd buf p;
  Buffer.contents buf

let exp_to_string e =
  let buf = Buffer.create 64 in
  pp_exp buf e;
  Buffer.contents buf

(* ---- Block-formatted predicate printing ---- *)

(* Column width threshold: if inline rendering fits, skip line breaks. *)
let block_width = 72

let rec pp_prd_block ?(min_bp = 0) ind buf p =
  (* Try inline first — if it fits, use it *)
  let inline = Buffer.create 128 in
  pp_prd ~min_bp inline p;
  if Buffer.length inline + ind <= block_width then
    Buffer.add_buffer buf inline
  else
    pp_prd_block_break ~min_bp ind buf p

and pp_prd_block_break ?(min_bp = 0) ind buf p =
  let pad = String.make ind ' ' in
  match p with
  | Binary (Imp, p1, p2) ->
    wrap buf (5 < min_bp) (fun () ->
      pp_prd_block ~min_bp:6 ind buf p1;
      Buffer.add_char buf '\n';
      Buffer.add_string buf pad;
      Buffer.add_string buf "\xe2\x87\x92 "; (* ⇒ *)
      pp_prd_block ~min_bp:5 ind buf p2)
  | Binary (And, _, _) ->
    let elts = flatten_conj p in
    pp_conj_left_block ~min_bp ind buf elts
  | Binary (Or, p1, p2) ->
    wrap buf (6 < min_bp) (fun () ->
      pp_prd_block ~min_bp:7 ind buf p1;
      Buffer.add_char buf '\n';
      Buffer.add_string buf pad;
      Buffer.add_string buf "\xe2\x88\xa8 "; (* ∨ *)
      pp_prd_block ~min_bp:6 ind buf p2)
  | Bind (binder, xs, body) ->
    let qsym = match binder with
      | Bang -> "`\xe2\x88\x80"
      | Forall -> "`\xe2\x99\xa2"
      | Forall2 -> "`\xe2\x99\xa1"
      | Exists   -> "`\xe2\x88\x83"
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
  (* Try inline first *)
  let inline = Buffer.create 128 in
  pp_conj_left ~min_bp inline elts;
  if Buffer.length inline + ind <= block_width then
    Buffer.add_buffer buf inline
  else
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
