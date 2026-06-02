(* pp2lp CLI: read one .replay file and emit either Lambdapi source or
   the rebuilt proof tree to stdout.  No filesystem orchestration. *)

let die fmt =
  Printf.ksprintf (fun s -> prerr_string s; prerr_newline (); exit 1) fmt

let with_replay_open fp f =
  try f fp with
  | Pp2lp.Parse_replay.Bad_replay m -> die "parse error in %s: %s" fp m
  | Pp2lp.Proof_tree.Bad_replay m  -> die "tree-build error in %s: %s" fp m
  | Pp2lp.Proof_tree.Bad_replay_partial (m, _) ->
    die "tree-build error in %s: %s" fp m
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

(* Like with_replay_open but renders the partial stack on a tree-build
   stack-residual error before exiting.  The partial residual is what
   you actually need to debug an arity / unknown-rule problem. *)
let tree_replay fp =
  try
    let replay = Pp2lp.Parse_replay.parse_file fp in
    let tree   = Pp2lp.Proof_tree.build replay.rules in
    Pp2lp.Proof_tree.pp_tree stdout tree
  with
  | Pp2lp.Parse_replay.Bad_replay m -> die "parse error in %s: %s" fp m
  | Pp2lp.Proof_tree.Bad_replay_partial (m, residual) ->
    Printf.eprintf "tree-build error in %s: %s\n" fp m;
    Printf.eprintf "--- residual stack (top first) ---\n";
    List.iter (fun n -> Pp2lp.Proof_tree.pp_tree stderr n) residual;
    exit 1
  | Pp2lp.Proof_tree.Bad_replay m  -> die "tree-build error in %s: %s" fp m
  | Failure m -> die "%s: %s" fp m
  | exn -> die "%s: %s" fp (Printexc.to_string exn)

(* Dump the parsed replay as the (rule, arg) list.  Useful when even
   the tree-build is suspect: it shows what the parser produced
   before any phantom filtering or arity dispatch. *)
let rules_replay fp =
  with_replay_open fp (fun fp ->
    let replay = Pp2lp.Parse_replay.parse_file fp in
    List.iter (fun ((rule_name, arg), _anno, line) ->
      let arg_s = match arg with
        | None -> ""
        | Some (Pp2lp.Syntax_pp.Pred p) ->
          Printf.sprintf "(%s)" (Pp2lp.Emit_pp.prd_to_pp p)
        | Some (Pp2lp.Syntax_pp.PipeArg (a, b)) ->
          Printf.sprintf "(%s | %s)"
            (Pp2lp.Emit_pp.prd_to_pp (Pp2lp.Syntax_pp.Lift a))
            (Pp2lp.Emit_pp.prd_to_pp (Pp2lp.Syntax_pp.Lift b))
      in
      let kind =
        if Pp2lp.Rule_db.is_known rule_name then
          if Pp2lp.Rule_db.is_phantom rule_name then "phantom"
          else Printf.sprintf "arity=%d" (Pp2lp.Rule_db.rule_arity rule_name)
        else "UNKNOWN"
      in
      Printf.printf "%4d  %-12s %-10s %s\n" line rule_name kind arg_s
    ) replay.rules)

let usage () =
  prerr_endline "Usage:";
  prerr_endline "  pp2lp emit [--map F] REPLAY  clean Lambdapi to stdout (+ provenance TSV to F)";
  prerr_endline "  pp2lp tree REPLAY     print rebuilt proof tree (or residual stack)";
  prerr_endline "  pp2lp rules REPLAY    dump parsed (rule, arg, kind) lines";
  prerr_endline "  pp2lp REPLAY          alias for: pp2lp emit REPLAY";
  prerr_endline "  pp2lp -h | --help     this help"

let () =
  match Array.to_list Sys.argv with
  | [_; ("--help" | "-help" | "-h")]      -> usage ()
  | [_; "emit"; "--map"; path; fp]        -> emit_replay ~map_file:path fp
  | [_; "emit"; fp]                       -> emit_replay fp
  | [_; "tree"; fp]                       -> tree_replay fp
  | [_; "rules"; fp]                      -> rules_replay fp
  | [_; fp] when fp <> "" && fp.[0] <> '-' -> emit_replay fp
  | _ -> usage (); exit 1
