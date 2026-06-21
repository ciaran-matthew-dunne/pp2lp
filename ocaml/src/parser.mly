%{
  open Syntax_pp

  (* Left-nest a comma-list into pairs: [a]→a, [a;b;c]→((a↦b)↦c).  PP renders
     a tuple `(a,b,c)` and the sides of a tuple equality `a,b = c,d` this way. *)
  let pairs = function
    | [e] -> e
    | e :: rest -> List.fold_left (fun a b -> Maplet (a, b)) e rest
    | [] -> assert false
%}

%token <string> SYMBOL
%token <int> NATURAL
%token <string> BIGNATURAL

%token EOF
%token PERIOD COMMA COLON DOTDOT MAPLET TILDE DOMRESTR RANRESTR
%token LPAREN RPAREN
%token LSQ RSQ
%token LBRACE RBRACE
%token LANGLE RANGLE

%token HYP TURNSTILE PIPE FIN
%token NOT AND OR IMP IFF EQ LEQ
%token PLUS MINUS TIMES POWER
%token INTER UNION
%token SEMI PERCENT NOTMEM SUBSET OVERRIDE TFUN PFUN PSURJ SIGMA INSTANCIATION BOOLOP
%token FORALL0 FORALL1 FORALL2 EXISTS

%nonassoc LIFT_EXP  (* lowest: raw_prd -> exp prefers shift over reduce *)
%nonassoc RPAREN    (* > LIFT_EXP: in `( exp )` shift into the exp-in-parens
                       rule rather than reducing raw_prd -> exp first.  Both
                       derivations yield the same AST (Lift exp); declaring
                       RPAREN makes menhir's default-shift explicit. *)
%nonassoc COMMA
%left IMP           (* PP spec priority 3: => *)
%left OR AND        (* PP spec priority 2: and, or (same level, left-assoc) *)
%left IFF           (* PP spec priority 1: <=> (tighter than and/or) *)
%right PERIOD       (* binder has narrow scope: !x.P and Q = (∀x.P) ∧ Q *)
%left UNION INTER   (* same level, left-assoc — like or/and: `s \/ t /\ s` is
                       `(s \/ t) /\ s`, mirroring how PP unfolds the membership *)
%left TFUN PFUN PSURJ OVERRIDE SEMI  (* uninterpreted set/relation operators *)
%left MAPLET DOMRESTR RANRESTR  (* B-Book: set-operator level, looser than .. *)
%left DOTDOT        (* B-Book: .. looser than +/- — e-f..g+f = (e-f)..(g+f) *)
%left PLUS MINUS
%left TIMES          (* coefficient binds tighter than +/- : 2*x + y = (2*x) + y *)
%right POWER         (* exponentiation binds tighter than * : a*b**2 = a*(b**2) *)
%nonassoc UMINUS
%nonassoc LSQ
%nonassoc TILDE     (* highest: postfix inverse binds tighter than every
                       operator — r~[s] = (r~)[s], -x~ = -(x~), a<|b~ = a<|(b~).
                       The `exp TILDE` rule inherits this precedence, so each
                       `exp OP exp . TILDE` state shifts (applies ~ first). *)
%nonassoc LPAREN    (* application `f(x)` binds tighter than every operator:
                       `-x(y)` = `-(x(y))`, `a/\b(c)` = `a/\(b(c))`.  Resolving
                       the `exp OP exp . LPAREN` states toward shift. *)

%start <line option> line_eof
%%
var_seq:
  | x = SYMBOL
  { [x] }
  | x = SYMBOL; COMMA; xs = var_seq
  { x :: xs }
exp:
  | x = SYMBOL
  { Var x }
  | i = NATURAL
  { Lit (string_of_int i) }
  | i = BIGNATURAL
  { Lit i }
  (* Function application.  A bare-symbol head keeps the named [App] form
     (preserves existing emission / free-var handling); any other head
     (r~(s), {}(s), (r;s)(x)) becomes a general [EApp]. *)
  | e = exp; LPAREN; es = exp_seq; RPAREN
  { match e with Var x -> App (x, es) | _ -> EApp (e, es) }
  | FIN; LPAREN; es = exp_seq; RPAREN
  { App ("FIN", es) }
  | e1 = exp; PLUS; e2 = exp
  { AOp (Add, e1, e2) }
  | e1 = exp; MINUS; e2 = exp
  { (* `-` is overloaded (arithmetic subtraction vs set difference) and the token
       is the same.  A set-literal operand can't be arithmetic, so it disambiguates
       to set difference; otherwise default to arithmetic (the common case).  A
       `s - t` between two non-literal sets stays ambiguous and remains arithmetic
       — that needs type information we don't have. *)
    match e1, e2 with
    | SetLit _, _ | _, SetLit _ -> SetOp ("set_diff", [e1; e2])
    | _ -> AOp (Sub, e1, e2) }
  | e1 = exp; TIMES; e2 = exp
  { SetOp ("prod", [e1; e2]) }   (* product (set ×, or arithmetic ·) *)
  | MINUS; e = exp %prec UMINUS
  { Neg e }
  (* PP parenthesises compound operands of unary minus (`-(-x)`, `-(2*x)`);
     accept a parenthesised expression in any exp position. *)
  | LPAREN; e = exp; RPAREN
  { e }
  (* A parenthesised comma-list is a left-nested tuple (pair):
     `(a,b,c)` = `((a|->b)|->c)`.  Distinct from the singleton above (≥2
     elements) so it does not clash with the parenthesised-predicate rule. *)
  | LPAREN; e = exp; COMMA; es = exp_seq; RPAREN
  { pairs (e :: es) }
  | e1 = exp; TFUN; e2 = exp
  { SetOp ("total_func", [e1; e2]) }
  | e1 = exp; PFUN; e2 = exp
  { SetOp ("partial_func", [e1; e2]) }
  | e1 = exp; PSURJ; e2 = exp
  { SetOp ("partial_surj", [e1; e2]) }
  | e1 = exp; OVERRIDE; e2 = exp
  { SetOp ("overriding", [e1; e2]) }
  | e1 = exp; SEMI; e2 = exp
  { SetOp ("relcomp", [e1; e2]) }
  | e1 = exp; POWER; e2 = exp
  { SetOp ("power", [e1; e2]) }
  | c = comprehension
  { c }
  | BOOLOP; LPAREN; p = prd; RPAREN
  { BoolOf p }   (* bool(P): predicate cast to a BOOL element *)
  | e1 = exp; LSQ; e2 = exp; RSQ
  { SetImage (e1, e2) }
  | e1 = exp; INTER; e2 = exp
  { Inter (e1, e2) }
  | e1 = exp; DOTDOT; e2 = exp
  { Range (e1, e2) }
  | e1 = exp; MAPLET; e2 = exp
  { Maplet (e1, e2) }
  | e1 = exp; DOMRESTR; e2 = exp
  { DomRestrict (e1, e2) }
  | e1 = exp; RANRESTR; e2 = exp
  { RanRestrict (e1, e2) }
  | e = exp; TILDE
  { Inverse e }
  | LBRACE; es = exp_seq; RBRACE
  { SetLit es }
  | LBRACE; RBRACE
  { SetLit [] }
  | e1 = exp; UNION; e2 = exp
  { Union (e1, e2) }
exp_seq:
  | e = exp
  { [e] }
  | e = exp; COMMA; es = exp_seq
  { e :: es }

(* Set-builder / aggregate binders: %(x).(P | E), SIGMA(x).(P | E).  The body
   is always `predicate | value`; the bound vars scope over both. *)
compr_op:
  | PERCENT { "set_lambda" }
  | SIGMA   { "sigma" }
compr_vars:
  | LPAREN; xs = var_seq; RPAREN { xs }
  | x = SYMBOL                   { [x] }
comprehension:
  | op = compr_op; xs = compr_vars; PERIOD;
      LPAREN; p = prd; PIPE; v = exp; RPAREN
  { Compr (op, xs, p, v) }

binder:
  | FORALL0 { Bang }
  | FORALL1 { Forall }
  | FORALL2 { Forall2 }
  | EXISTS  { Exists }
binding:
  | b = binder; x = SYMBOL; PERIOD; p = prd
  { Bind (b, [x], p) }
  | b = binder; LPAREN; xs = var_seq; RPAREN; PERIOD; p = prd
  { Bind (b, xs, p) }

prd:
  | p = raw_prd { p }
  | LPAREN; p = raw_prd; RPAREN { p }
raw_prd:
  | e = exp
  { Lift e } %prec LIFT_EXP
  | NOT; LPAREN; t = prd; RPAREN
  { Unary (Not,t) }
  | t1 = prd; IMP; t2 = prd
  { Binary (Imp,t1,t2) }
  | t1 = prd; IFF; t2 = prd
  { Binary (Iff,t1,t2) }
  | t1 = prd; AND; t2 = prd
  { Binary (And,t1,t2) }
  | t1 = prd; OR; t2 = prd
  { Binary (Or,t1,t2) }
  | es1 = exp_seq; EQ; es2 = exp_seq
  { Eq (pairs es1, pairs es2) }
  (* tuple eq `a,b = c,d` = `(a↦b) = (c↦d)`.  One benign shift/reduce conflict:
     a COMMA right after the RHS is shifted (extends the RHS tuple) rather than
     reduced (ending the equality).  Shift is correct for every form PP emits —
     tuple equalities are formula-final, and binder bodies are parenthesised, so
     the comma never belongs to an enclosing hyps list. *)
  | e1 = exp; LEQ; e2 = exp
  { Leq (e1, e2) }
  | e1 = exp; LANGLE; e2 = exp
  { Rel ("lt", [e1; e2]) }   (* strict less-than (uninterpreted).  Only `<`: PP
                                never emits a strict `>` (which would clash with
                                the rhs `<…>` closing delimiter). *)
  | es = exp_seq; COLON; e = exp
  { Mem (es,e)}
  | e1 = exp; SUBSET; e2 = exp
  { Rel ("subset", [e1; e2]) }
  | e1 = exp; NOTMEM; e2 = exp
  { Unary (Not, Mem ([e1], e2)) }
  | INSTANCIATION; LPAREN; p = prd; RPAREN
  { Unary (Instanciation, p) }
  | t = binding
  { t }


lhs_arg:
  | p = prd
  (* a bare expression arg parses (via [prd]) as `Lift e`; keep it an expression
     ([ExpArg]) rather than a lifted predicate — the consumer re-lifts if it wants
     a proposition.  Structured predicates stay [Pred]. *)
  { match p with Lift e -> ExpArg e | _ -> Pred p }
  | e1 = exp; PIPE; e2 = exp
  { PipeArg (e1, e2) }
lhs:
  | LSQ; FIN; LPAREN; p = prd; RPAREN; RSQ
  { ("FIN", Some (Pred p)) }
  | LSQ; str = SYMBOL; RSQ
  { (str, None) }
  | LSQ; str = SYMBOL; LPAREN; a = lhs_arg; RPAREN; RSQ
  { (str, Some a) }


(* Hypothesis predicates: restricted form that avoids COMMA ambiguity
   with exp_seq in membership. Multi-element membership (x,y: S) must
   be parenthesized at the top level of a hypothesis. *)
hyp_prd:
  | e = exp
  { Lift e }
  | LPAREN; p = raw_prd; RPAREN
  { p }
  | t = binding
  { t }
  | NOT; LPAREN; t = prd; RPAREN
  { Unary (Not, t) }
  | e1 = exp; EQ; e2 = exp
  { Eq (e1, e2) }
  | e1 = exp; LEQ; e2 = exp
  { Leq (e1, e2) }
  | e = exp; COLON; e2 = exp
  { Mem ([e], e2) }
hyps:
  | HYP { [] }
  | hs = hyps; COMMA; p = hyp_prd { p :: hs }
sequent:
  | LPAREN; h = hyps; TURNSTILE; p = prd; RPAREN
  { (h, p) }
fin_right:
  | FIN; LPAREN; p = prd;
      PIPE; s1 = sequent; PIPE; s2 = sequent;
      PIPE; i = NATURAL;
    RPAREN
  { Fin (p,s1,s2,i) }
rhs:
  | LANGLE; p = prd; RANGLE { Simple p }
  | LANGLE; r = fin_right; RANGLE { r }

line:
  | l = lhs; r = rhs { (l,r) }
line_eof:
  | EOF { None }
  | l = line { Some l }
