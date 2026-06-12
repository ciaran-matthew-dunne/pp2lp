
type uop =
  | Not
and bop =
  | Or | And | Imp | Iff
and aop =
  | Add | Sub
and binder =
  | Bang     (* !x. — PP's default universal quantifier *)
  | Forall   (* forall x. — keyword form *)
  | Forall2  (* forall2 x. — second-order *)
  | Exists   (* #x. — existential quantifier *)

type prd =
  | Lift of exp
  | Unary of uop * prd
  | Binary of bop * prd * prd
  | Bind of binder * string list * prd
  | Mem of exp list * exp
  | Eq of exp * exp
  | Leq of exp * exp
and exp =
  | Var of string
  | Nat of int
  | App of string * exp list
  | AOp of aop * exp * exp
  | Neg of exp
  | SetImage of exp * exp
  | Inter of exp * exp
  | Union of exp * exp
  | Range of exp * exp          (* B interval a..b (apero/EGALITE replays) *)
  | Maplet of exp * exp         (* ordered pair a|->b *)
  | Inverse of exp              (* relational inverse r~ (postfix) *)
  | SetLit of exp list          (* set extension {a,b,c}; [] is {} *)
  | DomRestrict of exp * exp    (* domain restriction S <| r *)
  | RanRestrict of exp * exp    (* range restriction r |> T *)

type arg =
  | Pred of prd
  | PipeArg of exp * exp
and sequent =
  prd list * prd
and lhs =
  string * arg option
and rhs =
  | Simple of prd
  | Fin of prd * sequent * sequent * int
and line =
  lhs * rhs

(* PP folds a repeated sum into a literal product: `x + x` is rendered `2*x`.
   B-arithmetic (B.lp) has no multiplication — a numeral is itself a repeated
   `𝟏 +` — so we desugar a literal coefficient straight back into the sum it
   denotes (`2*x` ↦ `x + x`), left-nested to match `+`'s left associativity.
   Every later stage then sees an ordinary sum, so the existing +/INS/AR
   machinery applies unchanged.  Genuine variable·variable products do not
   occur in PP arithmetic replays; we fail loudly rather than invent a term. *)
let mul_expand e1 e2 =
  let expand n e =
    if n <= 0 then Nat 0
    else
      let rec build k = if k = 1 then e else AOp (Add, build (k - 1), e) in
      build n
  in
  match e1, e2 with
  | Nat n, e | e, Nat n -> expand n e
  | _ -> failwith "syntax_pp.mul_expand: non-literal multiplication (n*e expected)"

(* Collapse consecutive same-binder Binds into one compound Bind.
   `!x. !y. P` parses as nested; PP's ALL2/ALL3 normalize that to a
   single compound `!(x,y). P`. We do the same at the goal level so
   the LP-side ALL7 and friends see a single Tuple n binder. *)
let rec flatten_binds = function
  | Bind (b, xs, Bind (b', ys, body)) when b = b' ->
    flatten_binds (Bind (b, xs @ ys, body))
  | Bind (b, xs, body) -> Bind (b, xs, flatten_binds body)
  | Unary (op, p) -> Unary (op, flatten_binds p)
  | Binary (op, p1, p2) -> Binary (op, flatten_binds p1, flatten_binds p2)
  | (Lift _ | Mem _ | Eq _ | Leq _) as p -> p

(* Capture-permissive substitution over PP-side AST.  Used by the
   emitter to instantiate hypothesis-search patterns at chosen witness
   variables (AXM9, NRM19): given the binder's pp-vars and the chosen
   witness's pp-vars, substitute one-for-one and compare structurally
   against in-scope hypotheses. *)
(* The single shallow [exp] traversal.  [map_exp f e] rebuilds [e] with [f]
   applied to each immediate sub-expression; [fold_exp f acc e] left-folds [f]
   over them.  This is the one place that enumerates every [exp] constructor,
   so a new one forces an update here (warning 8 is fatal) and every walker
   built on top — [subst_exp], [Emit_ctx.canon_exp], [Free_vars] — stays
   complete instead of silently dropping it. *)
let map_exp f = function
  | Var _ | Nat _ as e -> e
  | App (g, args) -> App (g, List.map f args)
  | AOp (o, a, b) -> AOp (o, f a, f b)
  | Neg e -> Neg (f e)
  | SetImage (a, b) -> SetImage (f a, f b)
  | Inter (a, b) -> Inter (f a, f b)
  | Union (a, b) -> Union (f a, f b)
  | Range (a, b) -> Range (f a, f b)
  | Maplet (a, b) -> Maplet (f a, f b)
  | Inverse e -> Inverse (f e)
  | SetLit es -> SetLit (List.map f es)
  | DomRestrict (a, b) -> DomRestrict (f a, f b)
  | RanRestrict (a, b) -> RanRestrict (f a, f b)

let fold_exp f acc = function
  | Var _ | Nat _ -> acc
  | App (_, args) -> List.fold_left f acc args
  | AOp (_, a, b) | SetImage (a, b) | Inter (a, b) | Union (a, b)
  | Range (a, b) | Maplet (a, b) | DomRestrict (a, b) | RanRestrict (a, b) ->
    f (f acc a) b
  | Neg e | Inverse e -> f acc e
  | SetLit es -> List.fold_left f acc es

(* Structural congruence for first-order matching: [Some] of the paired
   sub-expressions when [a] and [b] share the same constructor, payload, and
   arity; [None] otherwise (the leaves [Var]/[Nat] included — the matcher
   discriminates those itself).  Exhaustive, so a new constructor forces an
   update here too rather than silently failing to match. *)
let exp_congruence a b : (exp * exp) list option =
  match a, b with
  | Var _, _ | Nat _, _ -> None
  | App (f, xs), App (g, ys) when f = g && List.length xs = List.length ys ->
    Some (List.combine xs ys)
  | AOp (o, a1, a2), AOp (o', b1, b2) when o = o' -> Some [ (a1, b1); (a2, b2) ]
  | Neg a1, Neg b1 -> Some [ (a1, b1) ]
  | Inverse a1, Inverse b1 -> Some [ (a1, b1) ]
  | SetImage (a1, a2), SetImage (b1, b2) -> Some [ (a1, b1); (a2, b2) ]
  | Inter (a1, a2), Inter (b1, b2) -> Some [ (a1, b1); (a2, b2) ]
  | Union (a1, a2), Union (b1, b2) -> Some [ (a1, b1); (a2, b2) ]
  | Range (a1, a2), Range (b1, b2) -> Some [ (a1, b1); (a2, b2) ]
  | Maplet (a1, a2), Maplet (b1, b2) -> Some [ (a1, b1); (a2, b2) ]
  | DomRestrict (a1, a2), DomRestrict (b1, b2) -> Some [ (a1, b1); (a2, b2) ]
  | RanRestrict (a1, a2), RanRestrict (b1, b2) -> Some [ (a1, b1); (a2, b2) ]
  | SetLit xs, SetLit ys when List.length xs = List.length ys ->
    Some (List.combine xs ys)
  | (App _ | AOp _ | Neg _ | Inverse _ | SetImage _ | Inter _ | Union _
    | Range _ | Maplet _ | DomRestrict _ | RanRestrict _ | SetLit _), _ -> None

let rec subst_exp env = function
  | Var s -> (try List.assoc s env with Not_found -> Var s)
  | e -> map_exp (subst_exp env) e

let rec subst_prd env = function
  | Lift e -> Lift (subst_exp env e)
  | Unary (op, p) -> Unary (op, subst_prd env p)
  | Binary (op, p1, p2) -> Binary (op, subst_prd env p1, subst_prd env p2)
  | Bind (b, xs, body) ->
    let env' = List.filter (fun (k, _) -> not (List.mem k xs)) env in
    Bind (b, xs, subst_prd env' body)
  | Mem (es, e) -> Mem (List.map (subst_exp env) es, subst_exp env e)
  | Eq (e1, e2) -> Eq (subst_exp env e1, subst_exp env e2)
  | Leq (e1, e2) -> Leq (subst_exp env e1, subst_exp env e2)

let prd_of_rhs = function
  | Simple p -> p
  | Fin (p, _, _, _) -> p
