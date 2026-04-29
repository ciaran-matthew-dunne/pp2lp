(* Project-local utop init for `make repl`.
   Opens Stdlib (autoload is broken in this opam env) and Pp2lp.Repl_data
   so its bindings (og_27, og_replays, compare_builders, …) are available
   unqualified at the prompt. Provides short aliases [P] / [C] for the
   two proof_tree builders so you can compare them side by side:

     let lines = og_27;;
     let t  = P.build lines;;
     let t' = C.build lines;;
     let diffs = diffs_in "og";;

   Both modules have a `build` value, so they're aliased rather than
   `open`-ed to avoid shadowing.
*)
open Stdlib
open Pp2lp.Repl_data
module P = Pp2lp.Proof_tree
module C = Pp2lp.Proof_tree_cmd
