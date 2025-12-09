{
  open Parser
}

let symbol =
  ['a'-'z' 'A'-'Z']
  ['a'-'z' 'A'-'Z' '0'-'9' '_' '$']*

let digit = ['0'-'9']
let natural = digit+

rule token = parse
  (* punctuation *)
  | ',' { COMMA }
  | '.' { PERIOD }
  | ':' { COLON }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LSQ }
  | ']' { RSQ }
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
