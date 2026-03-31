%{
  open Syntax_pp
%}

%token <string> SYMBOL
%token <int> NATURAL

%token EOF
%token PERIOD COMMA COLON
%token LPAREN RPAREN
%token LSQ RSQ
%token LANGLE RANGLE

%token HYP TURNSTILE PIPE FIN
%token NOT AND OR IMP IFF EQ LEQ
%token PLUS MINUS
%token INTER UNION
%token FORALL0 FORALL1 FORALL2 EXISTS

%nonassoc LIFT_EXP  (* lowest: raw_prd -> exp prefers shift over reduce *)
%nonassoc COMMA
%left IMP           (* !x.P => Q = (∀x.P) => Q *)
%left IFF           (* !x.P <=> Q = (∀x.P) <=> Q *)
%left OR AND          (* PP spec: ∧ and ∨ have same priority (2), both left-assoc *)
%right PERIOD       (* binder has narrow scope: !x.P and Q = (∀x.P) ∧ Q *)
%left UNION
%left INTER
%left PLUS MINUS
%nonassoc UMINUS
%nonassoc LSQ

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
  { Nat i }
  | x = SYMBOL; LPAREN; es = exp_seq; RPAREN
  { App (x, es) }
  | FIN; LPAREN; es = exp_seq; RPAREN
  { App ("FIN", es) }
  | e1 = exp; PLUS; e2 = exp
  { AOp (Add, e1, e2) }
  | e1 = exp; MINUS; e2 = exp
  { AOp (Sub, e1, e2) }
  | MINUS; e = exp %prec UMINUS
  { Neg e }
  | e1 = exp; LSQ; e2 = exp; RSQ
  { SetImage (e1, e2) }
  | e1 = exp; INTER; e2 = exp
  { Inter (e1, e2) }
  | e1 = exp; UNION; e2 = exp
  { Union (e1, e2) }
exp_seq:
  | e = exp
  { [e] }
  | e = exp; COMMA; es = exp_seq
  { e :: es }

binder:
  | FORALL0 { Forall0 }
  | FORALL1 { Forall1 }
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
  | e1 = exp; EQ; e2 = exp
  { Eq (e1, e2) }
  | e1 = exp; LEQ; e2 = exp
  { Leq (e1, e2) }
  | es = exp_seq; COLON; e = exp
  { Mem (es,e)}
  | t = binding
  { t } %prec PERIOD


lhs_arg:
  | p = prd
  { Pred p }
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
