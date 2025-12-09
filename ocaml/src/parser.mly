%{
  open Syntax_pp
%}

%token <string> SYMBOL
%token <int> NATURAL

/* Delimiters */
%token PERIOD COMMA COLON
%token LPAREN RPAREN
%token LSQ RSQ
%token LANGLE RANGLE

/* Logical Connectives */
%token NOT AND OR IMP IFF EQ
%token FORALL0 FORALL1 FORALL2 EXISTS

/* PRECEDENCE AND ASSOCIATIVITY
   Sorted from Lowest (0) to Highest (11) based on your table.
*/

/* Priority 0 */
%left IMP               /* => */

/* Priority 1 */
%left IFF               /* <=> */

/* Priority 2 */
%left OR AND            /* or, and */

/* Priority 3 */
%nonassoc NOT           /* not */

/* Priority 4 */
%left EQ                /* = */
%nonassoc COLON         /* : (Matches priority of =, lower than comma) */

/* Priority 5 */
%left COMMA             /* , (Binds tightest: x,y:z -> (x,y):z) */

/* Priority 6 */
%nonassoc EXISTS        /* # */

/* Priority 7 */
%right PERIOD           /* . (Quantifier scope extends to the right) */

/* Priority 11 */
%nonassoc FORALL0 FORALL2 FORALL1 /* !, forall */

%start <term> term
%start <step * term> line

%%

/* --- RULES --- */

binder:
  | FORALL0 { Forall0 }
  | FORALL1 { Forall1 }
  | FORALL2 { Forall2 }
  | EXISTS  { Exists }

atom:
  | s = SYMBOL
  { Atom (s, []) }
  | s = SYMBOL; LPAREN; ts = tuple; RPAREN
  { Atom (s, List.rev ts) }

tuple:
  /* A tuple can be a single term, or a list separated by commas */
  | t = term
  { [t] }
  | ts = tuple; COMMA; t = term
  { t :: ts }

term:
  /* INLINED BINARY OPERATORS (Essential for precedence to work) */
  | t1 = term; EQ;  t2 = term { Binary (Eq,  t1, t2) }
  | t1 = term; AND; t2 = term { Binary (And, t1, t2) }
  | t1 = term; OR;  t2 = term { Binary (Or,  t1, t2) }
  | t1 = term; IMP; t2 = term { Binary (Imp, t1, t2) }
  | t1 = term; IFF; t2 = term { Binary (Iff, t1, t2) }

  /* UNARY OPERATORS */
  | NOT; LPAREN; t = term; RPAREN { Unary (Not, t) }
  /* Alternative if 'not p' is allowed without parens: */
  /* | NOT; t = term { Unary (Not, t) } */

  /* QUANTIFIERS */
  | b = binder; xs = binding; PERIOD; t = term
  { Bind (b, xs, t) }

  /* MEMBERSHIP / TYPING */
  /* Uses %prec COLON to ensure correct grouping vs COMMA */
  | ts = tuple; COLON; t = term %prec COLON
  { Mem (List.rev ts, t) }

  /* ATOMS */
  | p = atom { p }

vrb:
  | x = SYMBOL { [x] }
  | xs = vrb; COMMA; x = SYMBOL { x :: xs }

binding:
  | x = SYMBOL { [x] }
  | LPAREN; xs = vrb; RPAREN { List.rev xs }

index:
  | LPAREN; i = NATURAL; RPAREN { i }

step:
  | LSQ; str = SYMBOL; RSQ
  { (str, None) }
  | LSQ; str = SYMBOL; idx = index; RSQ
  { (str, Some (Index idx)) }
  | LSQ; str = SYMBOL; t = term; RSQ
  { (str, Some (Term t)) }

goal:
  | LANGLE; t = term; RANGLE { t }

line:
  | s = step; g = goal { (s,g) }
