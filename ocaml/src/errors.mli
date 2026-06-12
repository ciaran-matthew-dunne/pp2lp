(* Stable error-code prefixes for engine failures.  [fail code fmt …] raises
   `Failure "CODE: message"`; the CLI classifies by the leading `^E_[A-Z_]+:`
   prefix (regex fallback for the parse/tree exception channel and old logs).
   The code set is fixed: E_UNKNOWN_RULE, E_ARITY, E_DISPATCH, E_TREE_BUILD,
   E_PARSE, E_INS, E_EMIT. *)
val fail : string -> ('a, unit, string, 'b) format4 -> 'a
