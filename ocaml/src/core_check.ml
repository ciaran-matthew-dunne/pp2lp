(* Is a parsed replay confined to PP's FOL + LIA + membership core?

   PP normalises a goal by unfolding membership: a set constructor in
   predicate position (subset, a function space `f : A --> B`, a product or
   interval under `:`) is rewritten to its defining first-order form, so a
   fully-normalised replay mentions only logic, linear integer arithmetic, and
   membership into opaque sets.  Industrial (apero) goals, by contrast, carry
   irreducible set primitives — `dom`, `ran`, `card`, `perm`, `POW`, set
   enumerations, set-equation hypotheses like `s = A --> B` — that PP keeps as
   uninterpreted symbols (the emitter backs them with B.lp constants).  This
   module reports the first such non-core construct, so the generator can drop a
   contaminated apero replay rather than ship a proof over uninterpreted set ops.

   Allowed (core): the logical connectives/quantifiers, `=`/`<=`/`<` and integer
   arithmetic (`+ - *` coefficient, unary minus, literals), membership `t : S`
   and `t /: S`, set-equality `_eql_set`, pairing (maplet), `bool(P)`, and the
   NAT/INT context intervals `0..MAXINT` / `MININT..MAXINT`.

   Rejected (non-core): every [SetOp] (total_func, overriding, relcomp, prod,
   power), [Rel] other than `lt`, the relational term operators (set image,
   inter, union, inverse, domain/range restriction), set comprehension/λ,
   set enumeration, a non-boilerplate interval, and any [meta_ops] application
   (dom, ran, card, perm, iseq, seq, POW, id, …). *)

open Syntax_pp

(* The NAT/INT context definitions PP injects into every apero goal —
   `_eql_set(NAT, 0..MAXINT)` and `_eql_set(INT, MININT..MAXINT)` — are
   boilerplate, not goal structure, so their interval is exempt.  Recognise the
   two bound shapes by their endpoints; a genuine range (`1..n`, `1..s11`) has a
   variable endpoint and is not exempt. *)
let endpoint_name = function Lit s | Var s -> s | _ -> ""

let is_context_interval a b =
  List.mem (endpoint_name a) [ "0"; "MININT" ] && endpoint_name b = "MAXINT"

let ( <|> ) o f = match o with Some _ -> o | None -> f ()

(* `*` is overloaded: a Cartesian product `S * T` (set, non-core) or a folded
   coefficient `n * x` (LIA, core).  As in [Arith_proofs.prod_coeff], a literal
   operand marks the coefficient form. *)
let is_coeff_prod a b =
  (match a with Lit _ -> true | _ -> false)
  || (match b with Lit _ -> true | _ -> false)

(* First non-core construct in an expression, if any (a short label). *)
let rec noncore_exp = function
  | Var _ | Lit _ -> None
  | SetOp ("prod", [ a; b ]) when is_coeff_prod a b ->
    noncore_exp a <|> fun () -> noncore_exp b
  | SetOp (name, _) -> Some name
  | SetImage _ -> Some "set_image"
  | Inter _ -> Some "inter"
  | Union _ -> Some "union"
  | Inverse _ -> Some "inverse"
  | DomRestrict _ -> Some "dom_restrict"
  | RanRestrict _ -> Some "ran_restrict"
  | Compr (name, _, _, _) -> Some name
  | SetLit _ -> Some "set_enum"
  | Range (a, b) -> if is_context_interval a b then None else Some "interval"
  | App (f, _) when List.mem f meta_ops -> Some f
  | App (_, args) -> first_noncore args
  | EApp (h, args) -> noncore_exp h <|> fun () -> first_noncore args
  | AOp (_, a, b) -> noncore_exp a <|> fun () -> noncore_exp b
  | Neg e -> noncore_exp e
  | Maplet (a, b) -> noncore_exp a <|> fun () -> noncore_exp b
  | BoolOf p -> noncore_prd p

and first_noncore = function
  | [] -> None
  | e :: rest -> noncore_exp e <|> fun () -> first_noncore rest

and noncore_prd = function
  | Lift e -> noncore_exp e
  | Unary (_, p) -> noncore_prd p
  | Binary (_, p1, p2) -> noncore_prd p1 <|> fun () -> noncore_prd p2
  | Bind (_, _, body) -> noncore_prd body
  | Mem (es, e) -> first_noncore es <|> fun () -> noncore_exp e
  | Eq (a, b) | Leq (a, b) -> noncore_exp a <|> fun () -> noncore_exp b
  | Rel ("lt", es) -> first_noncore es        (* strict-< is LIA, not set *)
  | Rel (op, _) -> Some op                     (* subset, … *)

let noncore_arg = function
  | Pred p -> noncore_prd p
  | PipeArg (a, b) -> noncore_exp a <|> fun () -> noncore_exp b
  | ExpArg e -> noncore_exp e

(* All predicates a rule line presents: the resulting goal, plus the two
   sequents (hyps + goal) of a FIN finalisation, plus any rule argument. *)
let prds_of_rhs = function
  | Simple p -> [ p ]
  | Fin (p, (h1, g1), (h2, g2), _) -> (p :: g1 :: g2 :: h1) @ h2

(* First (replay line, construct) that leaves the core, scanning every rule. *)
let first_noncore_line (r : Parse_replay.replay) =
  List.find_map
    (fun ((_, arg), rhs, line) ->
      let from_prds =
        List.find_map noncore_prd (prds_of_rhs rhs) in
      let hit = from_prds <|> fun () -> Option.bind arg noncore_arg in
      Option.map (fun c -> (line, c)) hit)
    r.rules
