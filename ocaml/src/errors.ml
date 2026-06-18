(* Stable error-code prefixes for engine failures.

   [fail code fmt …] raises `Failure "CODE: message"` (via the same ksprintf
   idiom as the parse/tree `bad` helpers).  The CLI classifies a failure by the
   leading `^E_[A-Z_]+:` prefix, falling back to message-regex for the
   exception-based parse/tree channel and for older logs (see pp2lp).

   The code set is fixed — no new codes:
     E_UNKNOWN_RULE  a rule name not in the rule database
     E_ARITY         a rule used with the wrong number of children
     E_DISPATCH      an unsupported rule shape / dispatch arm
     E_TREE_BUILD    replay → proof-tree reconstruction failure
     E_PARSE         replay-line parse failure
     E_INS           the INS universal-instantiation contradiction search failed
     E_EMIT          any other emit-side failure (the CLI default) *)
let fail code fmt = Printf.ksprintf (fun s -> failwith (code ^ ": " ^ s)) fmt

(* A non-fatal emit-side warning.  Prints `WARNING: <message>` to stderr; the
   engine continues (exit 0) and the CLI's emit step scrapes these lines and
   surfaces them as the trace's warnings (see pp2lp `emit`). *)
let warn fmt = Printf.ksprintf (fun s -> Printf.eprintf "WARNING: %s\n%!" s) fmt
