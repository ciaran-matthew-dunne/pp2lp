(* Proof tree rebuilt from a parsed `.replay`.  The prefix/postfix replay
   grammar and the result-chain stack machine are internal; this exposes
   the tree type and the builder. *)

open Syntax_pp

type pp_tree =
  | Apply of {
      rule : string;
      arg : arg option;
      anno : rhs option;
      children : pp_tree list;
      (* 1-indexed line in the .replay this node's rule came from. *)
      src_line : int;
    }

(* Raised on a malformed replay. *)
exception Bad_replay of string

(** Rebuild the proof tree from a parsed replay's (rule, annotation, line)
    list.  Raises [Bad_replay] on a malformed one. *)
val build : (lhs * rhs * int) list -> pp_tree

(** The root node's annotation (the overall goal). *)
val anno_of : pp_tree -> rhs option
