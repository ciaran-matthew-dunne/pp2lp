(* pp2lp CLI: read one .replay file and emit Lambdapi source to stdout.
   No filesystem orchestration. *)

let die fmt =
  Printf.ksprintf (fun s -> prerr_string s; prerr_newline (); exit 1) fmt

let with_replay_open fp f =
  try f fp with
  | Pp2lp.Parse_replay.Bad_replay m -> die "parse error in %s: %s" fp m
  | Pp2lp.Proof_tree.Bad_replay m  -> die "tree-build error in %s: %s" fp m
  | Failure m -> die "%s: %s" fp m
  | exn -> die "%s: %s" fp (Printexc.to_string exn)

(* Side-channel provenance map: one TSV line per emitted primary tactic,
   `lp_line \t rule \t replay_line \t goal`.  Keeps the generated .lp clean —
   no comments — while the CLI can still map an error line back to its rule. *)
let write_map path prov =
  let oc = open_out path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
    List.iter (fun (line, (p : Pp2lp.Lp_tree.prov)) ->
      let g = String.map (fun c -> if c = '\t' || c = '\n' then ' ' else c) p.goal in
      Printf.fprintf oc "%d\t%s\t%d\t%s\n" line p.rule p.replay_line g) prov)

let emit_replay ?map_file fp =
  with_replay_open fp (fun fp ->
    let text, prov = Pp2lp.Reconstruct.reconstruct_symbol fp in
    print_string text;
    Option.iter (fun path -> write_map path prov) map_file)

(* Classify a replay as PP's FOL+LIA+membership core or not, for the gen-phase
   apero suite filter.  Prints `CORE` or `NONCORE <construct> <line>` to stdout
   (exit 0); a parse failure dies via [with_replay_open] (exit 1). *)
let core_check fp =
  with_replay_open fp (fun fp ->
    let r = Pp2lp.Parse_replay.parse_file fp in
    match Pp2lp.Core_check.first_noncore_line r with
    | None -> print_endline "CORE"
    | Some (line, c) -> Printf.printf "NONCORE\t%s\t%d\n" c line)

let usage () =
  prerr_endline "Usage:";
  prerr_endline "  pp2lp emit [--map F] REPLAY  clean Lambdapi to stdout (+ provenance TSV to F)";
  prerr_endline "  pp2lp core-check REPLAY      CORE | NONCORE <construct> <line> (gen-phase filter)";
  prerr_endline "  pp2lp REPLAY          alias for: pp2lp emit REPLAY";
  prerr_endline "  pp2lp -h | --help     this help"

let () =
  match Array.to_list Sys.argv with
  | [_; ("--help" | "-help" | "-h")]      -> usage ()
  | [_; "emit"; "--map"; path; fp]        -> emit_replay ~map_file:path fp
  | [_; "emit"; fp]                       -> emit_replay fp
  | [_; "core-check"; fp]                 -> core_check fp
  | [_; fp] when fp <> "" && fp.[0] <> '-' -> emit_replay fp
  | _ -> usage (); exit 1
