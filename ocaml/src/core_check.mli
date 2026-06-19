(* Is a parsed replay confined to PP's FOL + LIA + membership core, or does it
   retain a set-theoretic construct PP did not unfold (a function space, subset,
   product, restriction, comprehension, set enumeration, or a [meta_ops]
   application such as dom/ran/card/perm/POW)?  See [core_check.ml] for the exact
   boundary, including the NAT/INT context-interval exemption. *)

(** [first_noncore_line r] is [Some (line, construct)] for the first non-core
    construct in [r] — [line] is its 1-indexed `.replay` source line and
    [construct] a short label (e.g. "total_func", "perm", "interval") — or
    [None] when the whole replay is FOL + LIA + membership. *)
val first_noncore_line : Parse_replay.replay -> (int * string) option
