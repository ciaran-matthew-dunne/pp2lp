
type uop =
  | Not
  | Instanciation  (* PP's __INSTANCIATION(P) marker — logically P; kept as a
                      tag for the (future) FIN_INS evidence dispatch *)
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
  | Rel of string * exp list    (* uninterpreted Prop-valued operator applied
                                   directly: S <: T ↦ Rel ("subset", [S; T]) *)
and exp =
  | Var of string
  | Lit of string               (* an integer literal as a canonical decimal
                                   string.  Folds into an arithmetic constant when
                                   it fits a native int ([int_of_string_opt]); a
                                   too-big one (apero's 2⁶⁴ uint64 bounds) stays a
                                   symbolic atom, rendered via B.lp's int_lit. *)
  | App of string * exp list    (* B-function application f(x): a set of pairs
                                   applied via `eapp` to its argument(s) *)
  | EApp of exp * exp list      (* application of a non-symbol head: r~(s),
                                   {}(s), (r;s)(x) — emits `eapp <head> args` *)
  | SetOp of string * exp list  (* uninterpreted higher-order operator applied
                                   directly (NOT via eapp): S --> T, r <+ s,
                                   r ; s, S * T ↦ SetOp (name, [a; b]) *)
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
  | BoolOf of prd               (* bool(P): cast a predicate to a BOOL element *)
  | Compr of string * string list * prd * exp
        (* set-builder / aggregate binder: %(xs).(P | E) ↦ ("set_lambda",…),
           SIGMA(xs).(P | E) ↦ ("sigma",…).  Binds xs over both the predicate
           P and the value E; the string is the LP kernel symbol. *)

(* A rule's `[RULE(arg)]` argument from the replay.  [ExpArg] is a bare
   expression (AR9's solver-normalised F, …) — kept as an [exp], not shoehorned
   into [Pred] via a `Lift`; a rule that wants it as a proposition re-lifts it.
   [Pred] is a structured predicate (AR10's `a,b: f`, IMP5's antecedent, …);
   [PipeArg] the `a | b` two-expression form (AR3). *)
type arg =
  | Pred of prd
  | PipeArg of exp * exp
  | ExpArg of exp
and sequent =
  prd list * prd
and lhs =
  string * arg option
and rhs =
  | Simple of prd
  | Fin of prd * sequent * sequent * int
and line =
  lhs * rhs

(* B built-in set/relation operators.  These are "too big" to be object-level
   B-functions (sets of ordered pairs), so they are applied DIRECTLY (NOT via
   `eapp`) and carry their own arrow types in B.lp.  PP writes them with
   application syntax `op(x)`, indistinguishable from a B-function application,
   so the emitter keys on this list to pick direct application over `eapp`.
   Names are the LP symbols (after the PP→LP `_`-prefix renaming). *)
let meta_ops =
  [ "card"; "dom"; "ran"; "perm"; "iseq"; "seq"; "seq1";
    "POW"; "POW1"; "FIN"; "FIN1"; "id"; "sz"; "func" ]

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
  | (Lift _ | Mem _ | Eq _ | Leq _ | Rel _) as p -> p

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
(* [map_prd_exp]/[fold_prd_exp] carry an exp-function through a predicate's
   immediate expressions — the bridge [map_exp]/[fold_exp] need to descend into
   a [Compr]'s predicate (which is a [prd], not an [exp]). *)
let rec map_prd_exp f = function
  | Lift e -> Lift (f e)
  | Unary (op, p) -> Unary (op, map_prd_exp f p)
  | Binary (op, p1, p2) -> Binary (op, map_prd_exp f p1, map_prd_exp f p2)
  | Bind (b, xs, body) -> Bind (b, xs, map_prd_exp f body)
  | Mem (es, e) -> Mem (List.map f es, f e)
  | Eq (e1, e2) -> Eq (f e1, f e2)
  | Leq (e1, e2) -> Leq (f e1, f e2)
  | Rel (op, es) -> Rel (op, List.map f es)

let rec fold_prd_exp f acc = function
  | Lift e -> f acc e
  | Unary (_, p) -> fold_prd_exp f acc p
  | Binary (_, p1, p2) -> fold_prd_exp f (fold_prd_exp f acc p1) p2
  | Bind (_, _, body) -> fold_prd_exp f acc body
  | Mem (es, e) -> f (List.fold_left f acc es) e
  | Eq (e1, e2) | Leq (e1, e2) -> f (f acc e1) e2
  | Rel (_, es) -> List.fold_left f acc es

let map_exp f = function
  | Var _ | Lit _ as e -> e
  | App (g, args) -> App (g, List.map f args)
  | EApp (h, args) -> EApp (f h, List.map f args)
  | SetOp (g, args) -> SetOp (g, List.map f args)
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
  | BoolOf pred -> BoolOf (map_prd_exp f pred)
  | Compr (op, xs, pred, value) -> Compr (op, xs, map_prd_exp f pred, f value)

let fold_exp f acc = function
  | Var _ | Lit _ -> acc
  | App (_, args) -> List.fold_left f acc args
  | EApp (h, args) -> List.fold_left f (f acc h) args
  | SetOp (_, args) -> List.fold_left f acc args
  | AOp (_, a, b) | SetImage (a, b) | Inter (a, b) | Union (a, b)
  | Range (a, b) | Maplet (a, b) | DomRestrict (a, b) | RanRestrict (a, b) ->
    f (f acc a) b
  | Neg e | Inverse e -> f acc e
  | SetLit es -> List.fold_left f acc es
  | BoolOf pred -> fold_prd_exp f acc pred
  | Compr (_, _, pred, value) -> f (fold_prd_exp f acc pred) value

(* Structural congruence for first-order matching: [Some] of the paired
   sub-expressions when [a] and [b] share the same constructor, payload, and
   arity; [None] otherwise (the leaves [Var]/[Lit] included — the matcher
   discriminates those itself).  Exhaustive, so a new constructor forces an
   update here too rather than silently failing to match. *)
let exp_congruence a b : (exp * exp) list option =
  match a, b with
  | Var _, _ | Lit _, _ -> None
  | App (f, xs), App (g, ys) when f = g && List.length xs = List.length ys ->
    Some (List.combine xs ys)
  | EApp (h, xs), EApp (h', ys) when List.length xs = List.length ys ->
    Some ((h, h') :: List.combine xs ys)
  | SetOp (f, xs), SetOp (g, ys) when f = g && List.length xs = List.length ys ->
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
  (* Comprehensions never first-order match (the predicate is non-pattern);
     a search needing one fails loud rather than matching unsoundly. *)
  | (App _ | EApp _ | SetOp _ | AOp _ | Neg _ | Inverse _ | SetImage _ | Inter _
    | Union _ | Range _ | Maplet _ | DomRestrict _ | RanRestrict _ | SetLit _
    | BoolOf _ | Compr _), _ -> None

let rec subst_exp env = function
  | Var s -> (try List.assoc s env with Not_found -> Var s)
  | BoolOf pred -> BoolOf (subst_prd env pred)
  | Compr (op, xs, pred, value) ->                  (* capture-avoiding *)
    let env' = List.filter (fun (k, _) -> not (List.mem k xs)) env in
    Compr (op, xs, subst_prd env' pred, subst_exp env' value)
  | e -> map_exp (subst_exp env) e

and subst_prd env = function
  | Lift e -> Lift (subst_exp env e)
  | Unary (op, p) -> Unary (op, subst_prd env p)
  | Binary (op, p1, p2) -> Binary (op, subst_prd env p1, subst_prd env p2)
  | Bind (b, xs, body) ->
    let env' = List.filter (fun (k, _) -> not (List.mem k xs)) env in
    Bind (b, xs, subst_prd env' body)
  | Mem (es, e) -> Mem (List.map (subst_exp env) es, subst_exp env e)
  | Eq (e1, e2) -> Eq (subst_exp env e1, subst_exp env e2)
  | Leq (e1, e2) -> Leq (subst_exp env e1, subst_exp env e2)
  | Rel (op, es) -> Rel (op, List.map (subst_exp env) es)

(* Replace every occurrence of the sub-expression [from_e] with [to_e]
   throughout an expression / predicate.  First-order and structural: an
   expression equal to [from_e] is rewritten wholesale, otherwise we recurse
   into its children.  This generalises [subst_exp] from a variable to an
   arbitrary sub-term — used by the ECTR3/4 equality-substitution search where
   the rewritten side may be a compound term (e.g. `f(x)`), not just a
   variable.  Unlike [subst_exp] it is not capture-avoiding; callers apply it
   to quantifier-free goal atoms. *)
let rec replace_subexp from_e to_e e =
  if e = from_e then to_e else map_exp (replace_subexp from_e to_e) e

let replace_subexp_prd from_e to_e p =
  map_prd_exp (replace_subexp from_e to_e) p

let prd_of_rhs = function
  | Simple p -> p
  | Fin (p, _, _, _) -> p

(* MSB-first binary digits (leading digit 1) of a positive decimal string.
   Long division by two, so it handles literals past native int (apero's 2⁶⁴
   uint64 bounds).  Emitted `from_int` ℤ literals use this binary Stdlib.Pos
   form — `Zpos (O/I … H)` — never a unary `𝟏`-sum, which would blow up. *)
let pos_bits (decimal : string) : int list =
  let halve s =
    let buf = Buffer.create (String.length s) and rem = ref 0 and seen = ref false in
    String.iter (fun ch ->
      let d = !rem * 10 + (Char.code ch - Char.code '0') in
      let q = d / 2 in
      if q <> 0 || !seen then begin
        Buffer.add_char buf (Char.chr (q + Char.code '0')); seen := true
      end;
      rem := d mod 2) s;
    let q = Buffer.contents buf in
    ((if q = "" then "0" else q), !rem)
  in
  let rec go s acc =
    if s = "0" then acc
    else let q, b = halve s in go q (b :: acc)
  in
  go decimal []
