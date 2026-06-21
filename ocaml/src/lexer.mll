{
  open Parser
}

(* A leading '_' is significant: PP emits identifiers like `_eql_set`, `_pj1`
   (handled by name in free_vars.ml / pp_lp.ml).  Without '_' in the start class
   the lexer skipped it char-by-char (one "unexpected char '_'" warning each). *)
let symbol =
  ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '$']*
let digit = ['0'-'9']
let natural = digit+

rule token = parse
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
  (* punctuation *)
  | ',' { COMMA }
  | ".." { DOTDOT }   (* interval a..b — must precede '.' (maximal munch) *)
  | '.' { PERIOD }
  | ':' { COLON }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LSQ }
  | ']' { RSQ }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '~' { TILDE }
  | ';' { SEMI }      (* relational composition r;s *)
  | '%' { PERCENT }   (* set-builder / lambda %(x).(P|E) *)
  | "/:" { NOTMEM }   (* not-member  x /: S *)
  (* angle brackets and comparison — longest match handles <=>/<=/<:/<+/<  *)
  | "<=>" { IFF }
  | "<="  { LEQ }
  | "<:"  { SUBSET }    (* subset  S <: T *)
  | "<+"  { OVERRIDE }  (* relational override r <+ s *)
  | "+->>" { PSURJ }    (* partial surjection  S +->> T (before "+->": maximal munch) *)
  | "-->" { TFUN }      (* total-function space   S --> T *)
  | "+->" { PFUN }      (* partial-function space S +-> T *)
  | '<'   { LANGLE }
  | '>'   { RANGLE }
  (* FIN/sequents.  "|->" (maplet) must precede "|-" (turnstile): maximal
     munch otherwise lexes `x|->y` as TURNSTILE RANGLE.  "<|"/"|>" are B's
     domain/range restriction (apero equality-prover annotations). *)
  | "|->" { MAPLET }
  | "<|"  { DOMRESTR }
  | "|>"  { RANRESTR }
  | "|-"  { TURNSTILE }
  | "|"   { PIPE }
  | "Hyp" { HYP }
  | "FIN" { FIN }
  (* logical connectives *)
  | "not" { NOT }
  | "and" { AND }
  | "or"  { OR }
  | "=>"  { IMP }
  | '='   { EQ }
  (* arithmetic *)
  | '+'   { PLUS }
  | '-'   { MINUS }
  | "**"  { POWER }   (* exponentiation a**b (must precede '*') *)
  | '*'   { TIMES }   (* PP renders a folded sum n·x as `n*x` (coefficient form) *)
  (* set operators *)
  | "/\\" { INTER }
  | "\\/" { UNION }
  (* binders *)
  | "#"        { EXISTS  }
  | '!'        { FORALL0 }
  | "forall"   { FORALL1 }
  | "forall2"  { FORALL2 }
  (* aggregate binder + the apero instantiation marker (keywords before the
     general `symbol` rule; equal-length ties resolve to the earliest rule) *)
  | "SIGMA"           { SIGMA }
  | "bool"            { BOOLOP }
  | "__INSTANCIATION" { INSTANCIATION }
  (* literals *)
  | symbol as s  { SYMBOL s }
  | natural as i
      { match int_of_string_opt i with
        | Some n -> NATURAL n
        | None -> BIGNATURAL i }   (* 2⁶⁴ uint64 bounds overflow native int *)
  | [' ' '\t' '\r'] { token lexbuf }
  | _ as c { Printf.eprintf "warning: skipping unexpected char '%c'\n" c; token lexbuf }
