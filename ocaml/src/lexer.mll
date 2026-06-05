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
  | '.' { PERIOD }
  | ':' { COLON }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LSQ }
  | ']' { RSQ }
  (* angle brackets and comparison — longest match handles <=>/<=/<  *)
  | "<=>" { IFF }
  | "<="  { LEQ }
  | '<'   { LANGLE }
  | '>'   { RANGLE }
  (* FIN/sequents *)
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
  | '*'   { TIMES }   (* PP renders a folded sum n·x as `n*x` (coefficient form) *)
  (* set operators *)
  | "/\\" { INTER }
  | "\\/" { UNION }
  (* binders *)
  | "#"        { EXISTS  }
  | '!'        { FORALL0 }
  | "forall"   { FORALL1 }
  | "forall2"  { FORALL2 }
  (* literals *)
  | symbol as s  { SYMBOL s }
  | natural as i { NATURAL (int_of_string i) }
  | [' ' '\t' '\r'] { token lexbuf }
  | _ as c { Printf.eprintf "warning: skipping unexpected char '%c'\n" c; token lexbuf }
