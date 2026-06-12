
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
let rec subst_exp env = function
  | Var s -> (try List.assoc s env with Not_found -> Var s)
  | Nat n -> Nat n
  | App (f, args) -> App (f, List.map (subst_exp env) args)
  | AOp (op, e1, e2) -> AOp (op, subst_exp env e1, subst_exp env e2)
  | Neg e -> Neg (subst_exp env e)
  | SetImage (e1, e2) -> SetImage (subst_exp env e1, subst_exp env e2)
  | Inter (e1, e2) -> Inter (subst_exp env e1, subst_exp env e2)
  | Range (e1, e2) -> Range (subst_exp env e1, subst_exp env e2)
  | Maplet (e1, e2) -> Maplet (subst_exp env e1, subst_exp env e2)
  | Inverse e -> Inverse (subst_exp env e)
  | SetLit es -> SetLit (List.map (subst_exp env) es)
  | DomRestrict (e1, e2) -> DomRestrict (subst_exp env e1, subst_exp env e2)
  | RanRestrict (e1, e2) -> RanRestrict (subst_exp env e1, subst_exp env e2)
  | Union (e1, e2) -> Union (subst_exp env e1, subst_exp env e2)

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
