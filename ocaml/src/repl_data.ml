(* REPL test data: parsers for bench replays, exposed under
   [Pp2lp.Repl_data] for interactive exploration via `make repl`.

   No eager parsing happens at module load — these are functions, so
   the library has zero runtime cost when loaded by the production
   pp2lp binary.

   Typical use:

     let lines = Pp2lp.Repl_data.og "27";;            (* one replay      *)
     let all   = Pp2lp.Repl_data.all_og ();;          (* every og replay *)
     let t1    = Pp2lp.Proof_tree.build lines;;
     let t2    = Pp2lp.Proof_tree_cmd.build lines;;
*)

let project_root () =
  try Sys.getenv "PP2LP_ROOT"
  with Not_found -> Sys.getcwd ()

let replay_path suite name =
  Filename.concat (project_root ())
    (Printf.sprintf "bench/%s/%s.replay" suite name)

let parse suite name = Parse_pp.parse_pp_replay (replay_path suite name)

let og           name = parse "og"           name
let claude       name = parse "claude"       name
let claude_arith name = parse "claude-arith" name
let prv          name = parse "prv"          name

(* List the replay stem names ("01", "02", …) under bench/<suite>/.
   Empty list if the directory is missing. *)
let names_of suite =
  let dir = Filename.concat (project_root ()) ("bench/" ^ suite) in
  try
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun n -> Filename.check_suffix n ".replay")
    |> List.map (fun n -> Filename.chop_suffix n ".replay")
    |> List.sort compare
  with Sys_error _ -> []

(* Every replay in a suite, parsed eagerly, as (name, lines) pairs.
   Replays that fail to parse are silently dropped — flag-and-forget
   for REPL use. *)
let all_in suite =
  names_of suite
  |> List.filter_map (fun n ->
       try Some (n, parse suite n) with _ -> None)

let all_og ()           = all_in "og"
let all_claude ()       = all_in "claude"
let all_claude_arith () = all_in "claude-arith"
let all_prv ()          = all_in "prv"

(* Eager samples — pre-evaluated at module load so the REPL never has
   to type `()` or `[]` (utop-on-this-opam doesn't auto-open Stdlib).
   Loading cost is ~30 og replays + 30 claude-arith etc.; trivial. *)
let og_replays  = all_in "og"
let og_names    = List.map fst og_replays
let og_27       = try parse "og" "27" with _ -> []
let og_05       = try parse "og" "05" with _ -> []

(* Compare both proof_tree builders on the same input; returns
   (root1, root2, equal). Returns ("ERR", msg, false) if either raises. *)
let compare_builders lines =
  let root_of_apply = function
    | Proof_tree.Apply { rule; _ } -> rule
  in
  let root_of_apply_cmd = function
    | Proof_tree_cmd.Apply { rule; _ } -> rule
  in
  try
    let r1 = root_of_apply (Proof_tree.build lines) in
    let r2 = root_of_apply_cmd (Proof_tree_cmd.build lines) in
    (r1, r2, String.equal r1 r2)
  with e ->
    ("ERR", Printexc.to_string e, false)

(* Apply [compare_builders] across every replay in a suite, returning
   only the disagreements as (name, root1, root2) triples. *)
let diffs_in suite =
  all_in suite
  |> List.filter_map (fun (name, lines) ->
       let (r1, r2, eq) = compare_builders lines in
       if eq then None else Some (name, r1, r2))
