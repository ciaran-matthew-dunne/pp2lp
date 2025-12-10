{
  open Parser
}

let symbol =
  ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '$']*
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
  | '<' { LANGLE }
  | '>' { RANGLE }
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
  | "<=>" { IFF }
  | '='   { EQ }
  (* binders *)
  | "#"        { EXISTS  }
  | '!'        { FORALL0 }
  | "forall"   { FORALL1 }
  | "forall2"  { FORALL2 }
  (* literals *)
  | symbol as s  { SYMBOL s }
  | natural as i { NATURAL (int_of_string i) }
  | _ { token lexbuf }
