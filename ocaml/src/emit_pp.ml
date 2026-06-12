open Syntax_pp

(* Expression precedence levels (higher = tighter binding) *)
let exp_prec = function
  | Union _ -> 1
  | Inter _ -> 2
  | Maplet _ | DomRestrict _ | RanRestrict _ -> 3   (* B-Book: set-op level *)
  | Range _ -> 4              (* B-Book: .. looser than +/- *)
  | AOp _ -> 5
  | Neg _ -> 6
  | SetImage _ | Inverse _ -> 7
  | App _ | Var _ | Nat _ | SetLit _ -> 8

(* ---- Expression → PP text ---- *)

let rec exp_to_pp_buf ?(parent_prec=0) buf e =
  let prec = exp_prec e in
  let needs_parens = prec < parent_prec in
  if needs_parens then Buffer.add_char buf '(';
  (match e with
  | Var s -> Buffer.add_string buf s
  | Nat n -> Buffer.add_string buf (string_of_int n)
  | App (f, args) ->
    Buffer.add_string buf f;
    Buffer.add_char buf '(';
    List.iteri (fun i a ->
      if i > 0 then Buffer.add_char buf ',';
      exp_to_pp_buf ~parent_prec:0 buf a) args;
    Buffer.add_char buf ')'
  | AOp (Add, e1, e2) ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_char buf '+';
    exp_to_pp_buf ~parent_prec:(prec+1) buf e2
  | AOp (Sub, e1, e2) ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_char buf '-';
    exp_to_pp_buf ~parent_prec:(prec+1) buf e2
  | Neg e1 ->
    Buffer.add_string buf "-";
    exp_to_pp_buf ~parent_prec:(prec+1) buf e1
  | SetImage (e1, e2) ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_char buf '[';
    exp_to_pp_buf ~parent_prec:0 buf e2;
    Buffer.add_char buf ']'
  | Inter (e1, e2) ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_string buf "/\\";
    exp_to_pp_buf ~parent_prec:(prec+1) buf e2
  | Union (e1, e2) ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_string buf "\\/";
    exp_to_pp_buf ~parent_prec:(prec+1) buf e2
  | Range (e1, e2) ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_string buf "..";
    exp_to_pp_buf ~parent_prec:(prec+1) buf e2
  | Maplet (e1, e2) ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_string buf "|->";
    exp_to_pp_buf ~parent_prec:(prec+1) buf e2
  | DomRestrict (e1, e2) ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_string buf "<|";
    exp_to_pp_buf ~parent_prec:(prec+1) buf e2
  | RanRestrict (e1, e2) ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_string buf "|>";
    exp_to_pp_buf ~parent_prec:(prec+1) buf e2
  | Inverse e1 ->
    exp_to_pp_buf ~parent_prec:prec buf e1;
    Buffer.add_char buf '~'
  | SetLit es ->
    Buffer.add_char buf '{';
    List.iteri (fun i e ->
      if i > 0 then Buffer.add_char buf ',';
      exp_to_pp_buf ~parent_prec:0 buf e) es;
    Buffer.add_char buf '}');
  if needs_parens then Buffer.add_char buf ')'

(* ---- Predicate → PP text ---- *)

(* ~parens: whether to wrap Binary connectives in (...).
   false when caller already provides parens (binder body, not() body). *)
and prd_to_pp_buf ?(parens=true) buf p =
  match p with
  | Lift (Var "VRAI") | Lift (Var "TRUE") ->
    Buffer.add_string buf "btrue"
  | Lift (Var "FAUX") | Lift (Var "FALSE") ->
    Buffer.add_string buf "bfalse"
  | Lift (App (f, args)) ->
    List.iteri (fun i a ->
      if i > 0 then Buffer.add_char buf ',';
      exp_to_pp_buf ~parent_prec:0 buf a) args;
    Buffer.add_char buf ':';
    Buffer.add_string buf f
  | Lift e ->
    exp_to_pp_buf ~parent_prec:0 buf e
  | Unary (Not, p1) ->
    Buffer.add_string buf "not(";
    prd_to_pp_buf ~parens:false buf p1;
    Buffer.add_char buf ')'
  | Binary (bop, p1, p2) ->
    let sym = match bop with
      | And -> " and " | Or -> " or "
      | Imp -> " => " | Iff -> " <=> "
    in
    if parens then Buffer.add_char buf '(';
    prd_to_pp_buf buf p1;
    Buffer.add_string buf sym;
    prd_to_pp_buf buf p2;
    if parens then Buffer.add_char buf ')'
  | Eq (e1, e2) ->
    exp_to_pp_buf ~parent_prec:0 buf e1;
    Buffer.add_char buf '=';
    exp_to_pp_buf ~parent_prec:0 buf e2
  | Leq (e1, e2) ->
    exp_to_pp_buf ~parent_prec:0 buf e1;
    Buffer.add_string buf "<=";
    exp_to_pp_buf ~parent_prec:0 buf e2
  | Mem (es, e) ->
    List.iteri (fun i a ->
      if i > 0 then Buffer.add_char buf ',';
      exp_to_pp_buf ~parent_prec:0 buf a) es;
    Buffer.add_char buf ':';
    exp_to_pp_buf ~parent_prec:0 buf e
  | Bind (binder, xs, body) ->
    let qsym = match binder with
      | Bang -> "!"
      | Forall -> "forall"
      | Forall2 -> "forall2"
      | Exists -> "#"
    in
    Buffer.add_string buf qsym;
    (* PP always parenthesises the bound vars — `forall(x)`, `!(x,y)`, `#(x)` —
       even for a single variable, so render to match (no bare `forallx`). *)
    Buffer.add_char buf '(';
    List.iteri (fun i x ->
      if i > 0 then Buffer.add_char buf ',';
      Buffer.add_string buf x) xs;
    Buffer.add_char buf ')';
    Buffer.add_char buf '.';
    Buffer.add_char buf '(';
    prd_to_pp_buf ~parens:false buf body;
    Buffer.add_char buf ')'

(* ---- Public API ---- *)

let prd_to_pp p =
  let buf = Buffer.create 256 in
  prd_to_pp_buf buf p;
  Buffer.contents buf
