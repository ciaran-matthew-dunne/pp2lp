%{
  open PP_Syntax
%}


%token <string> SYMBOL
%token <int> INT

%token AND OR NOT IMP IFF NOT ALL EX EQ

%token PERIOD
%token LPAREN RPAREN
%token LANGLE RANGLE
%token LSQ RSQ

%%
index:
  | LPAREN; i = INT; RPAREN { i }

rule_app:
  | LSQ;
      str = STRING;
      idx_opt = option(idx);
    RSQ
  { (str, idx_opt)  }

goal:
  | LANGLE; prd; RANGLE
  { prd }

prd:
  | p = prd; AND; q = prd { And p q }
  | p = prd; OR; q = prd { Or p q }
  | p = prd; IMP; q = prd { Imp p q }
  | p = prd; IFF; q = prd { Iff p q }
  | NOT; p = prd { Not p }
  | FORALL; xs = vrb; PERIOD; p = prd
    { All xs p }
  | EXISTS; xs = vrb; PERIOD; p = prd
    { Exi xs p }
  | e1 = exp; EQ; e2 = exp
    { Eq e1 e2 }
  | frm
    { Formula frm }
