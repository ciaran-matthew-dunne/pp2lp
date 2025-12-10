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
%token NOT AND OR IMP IFF EQ
%token FORALL0 FORALL1 FORALL2 EXISTS

%left IMP
%left IFF
%left OR AND

%right PERIOD
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
  | x = SYMBOL; LPAREN; xs = var_seq; RPAREN
  { App (x, List.map (fun x -> Var x) xs) }
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
  { Lift e }
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
  | es = exp_seq; COLON; e = exp
  { Mem (es,e)}
  | t = binding
  { t }


index:
  | LPAREN; i = NATURAL; RPAREN { i }
lhs:
  | LSQ; FIN; LPAREN; p = prd; RPAREN; RSQ
  { ("FIN", Some (Pred p)) }
  | LSQ; str = SYMBOL; RSQ
  { (str, None) }
  | LSQ; str = SYMBOL; idx = index; RSQ
  { (str, Some (Index idx)) }
  | LSQ; str = SYMBOL; p = prd; RSQ
  { (str, Some (Pred p)) }


hyps:
  | HYP { [] }
  | hs = hyps; COMMA; p = prd { p :: hs }
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
