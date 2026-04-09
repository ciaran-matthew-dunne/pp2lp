let usage () =
  Printf.eprintf "Usage: pp2lp <command> [options] [files...]\n\n";
  Printf.eprintf "Commands:\n";
  Printf.eprintf "  emit  FILE...   Emit Lambdapi .lp to stdout\n";
  Printf.eprintf "  check FILE...   Emit .lp + run lambdapi check\n";
  Printf.eprintf "  batch DIR       Batch check all .replay files in DIR\n";
  Printf.eprintf "  parse FILE...   Parse replay files (diagnostics only)\n";
  Printf.eprintf "  prove FORMULA   Send formula to PP, emit LP proof\n";
  Printf.eprintf "  synth FILE DIR  Generate .but files from goals file into DIR\n"

let cmd_emit () =
  let files = ref [] in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv [] (fun f -> files := f :: !files)
    "Usage: pp2lp emit file1.replay ...";
  let files = List.rev !files in
  (* Emit header once, then all symbols *)
  print_string Pp2lp.Emit_lp.lp_header;
  print_char '\n';
  List.iter (fun fp ->
    try
      let content = Pp2lp.Reconstruct.reconstruct_symbol fp in
      print_string content;
      print_char '\n'
    with exn ->
      Printf.eprintf "ERROR: %s: %s\n" fp (Printexc.to_string exn)
  ) files

let cmd_check () =
  let files = ref [] in
  let lp_dir = ref "lp/gen" in
  let lp_pkg_dir = ref "lp" in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    ["--lp-dir", Arg.Set_string lp_dir, "Output directory for .lp files (default: lp/gen)";
     "--lp-pkg-dir", Arg.Set_string lp_pkg_dir, "Directory containing lambdapi.pkg (default: lp)"]
    (fun f -> files := f :: !files)
    "Usage: pp2lp check [--lp-dir DIR] [--lp-pkg-dir DIR] file1.replay ...";
  let files = List.rev !files in
  Pp2lp.Check.ensure_dir !lp_dir;
  let exit_code = ref 0 in
  List.iter (fun fp ->
    match Pp2lp.Check.check_replay ~lp_dir:!lp_dir ~lp_pkg_dir:!lp_pkg_dir fp with
    | Pp2lp.Check.Pass { name; elapsed; _ } ->
      Printf.printf " OK   %s  (%s)\n" name (Pp2lp.Check.format_time elapsed)
    | Pp2lp.Check.Fail { name; output; elapsed; _ } ->
      Printf.printf "FAIL  %s  (%s)\n" name (Pp2lp.Check.format_time elapsed);
      let lines = String.split_on_char '\n' (String.trim output) in
      List.iter (fun line ->
        if String.length line > 0 then
          Printf.printf "  | %s\n" line
      ) lines;
      exit_code := 1
    | Pp2lp.Check.Emit_error { name; msg } ->
      Printf.printf "EMIT  %s\n  | %s\n" name msg;
      exit_code := 1
  ) files;
  exit !exit_code

let cmd_batch () =
  let filter = ref None in
  let lp_dir = ref "lp/gen" in
  let lp_pkg_dir = ref "lp" in
  let no_cache = ref false in
  let cache_file = ref ".pp2lp-cache" in
  let dir = ref "" in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    ["--filter", Arg.String (fun s -> filter := Some s), "Filter replays by prefix";
     "--lp-dir", Arg.Set_string lp_dir, "Output directory for .lp files (default: lp/gen)";
     "--lp-pkg-dir", Arg.Set_string lp_pkg_dir, "Directory containing lambdapi.pkg (default: lp)";
     "--no-cache", Arg.Set no_cache, "Ignore cache, recheck all files";
     "--cache-file", Arg.Set_string cache_file, "Cache file path (default: .pp2lp-cache)"]
    (fun d -> dir := d)
    "Usage: pp2lp batch [options] DIR";
  if !dir = "" then begin
    Printf.eprintf "Error: batch requires a directory argument\n";
    exit 1
  end;
  let cfg = Pp2lp.Batch.{
    replay_dir = !dir;
    lp_dir = !lp_dir;
    lp_pkg_dir = !lp_pkg_dir;
    filter = !filter;
    use_cache = not !no_cache;
    cache_file = !cache_file;
  } in
  exit (Pp2lp.Batch.run cfg)

let cmd_parse () =
  let files = ref [] in
  let verbose = ref false in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    ["-v", Arg.Set verbose, "Verbose output"]
    (fun f -> files := f :: !files)
    "Usage: pp2lp parse [-v] file1.replay ...";
  let files = List.rev !files in
  let ok = ref 0 in
  let fail = ref 0 in
  List.iter (fun fp ->
    let lines = Pp2lp.Parse_pp.parse_pp_replay fp in
    let n = List.length lines in
    if n > 0 then begin
      if !verbose then
        Printf.printf "  OK: %s (%d lines)\n" fp n;
      incr ok
    end else begin
      Printf.printf "  FAIL: %s (0 lines)\n" fp;
      incr fail
    end
  ) files;
  Printf.printf "\nResults: %d ok, %d failed, %d total\n" !ok !fail (!ok + !fail)

let parse_formula s =
  let line = Printf.sprintf "[STOP] <%s>" s in
  match Pp2lp.Parse_pp.parse_pp_string line with
  | Some (_, Pp2lp.Syntax_pp.Simple p) -> Some p
  | _ -> None

let cmd_prove () =
  let name = ref "pp2lp_query" in
  let formula_str = ref "" in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    ["--name", Arg.Set_string name, "Symbol name for the proof (default: pp2lp_query)"]
    (fun s -> formula_str := s)
    "Usage: pp2lp prove [--name NAME] FORMULA";
  if !formula_str = "" then begin
    Printf.eprintf "Error: prove requires a formula argument\n";
    Printf.eprintf "Example: pp2lp prove '(p and q) => (q and p)'\n";
    exit 1
  end;
  match parse_formula !formula_str with
  | None ->
    Printf.eprintf "Error: failed to parse formula: %s\n" !formula_str;
    exit 1
  | Some formula ->
    (try
      let output = Pp2lp.Gen_but.prove ~name:!name formula in
      print_string output
    with Failure msg ->
      Printf.eprintf "Error: %s\n" msg;
      exit 1)

let cmd_synth () =
  let goals_file = ref "" in
  let out_dir = ref "" in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  let pos = ref 0 in
  Arg.parse_argv argv []
    (fun s ->
      match !pos with
      | 0 -> goals_file := s; incr pos
      | 1 -> out_dir := s; incr pos
      | _ -> Printf.eprintf "Warning: extra argument ignored: %s\n" s)
    "Usage: pp2lp synth GOALS_FILE OUTPUT_DIR";
  if !goals_file = "" || !out_dir = "" then begin
    Printf.eprintf "Usage: pp2lp synth GOALS_FILE OUTPUT_DIR\n";
    exit 1
  end;
  (* Ensure output directory exists *)
  (try Unix.mkdir !out_dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  (* Read goals file *)
  let ic = open_in !goals_file in
  let ok = ref 0 in
  let fail = ref 0 in
  (try while true do
    let line = input_line ic in
    let trimmed = String.trim line in
    (* Skip comments and blank lines *)
    if trimmed = "" || trimmed.[0] = '#' then ()
    else begin
      (* Split: first token is name, rest is formula *)
      match String.index_opt trimmed ' ' with
      | None ->
        Printf.eprintf "  SKIP: no formula after name: %s\n" trimmed;
        incr fail
      | Some i ->
        let name = String.sub trimmed 0 i in
        let formula_str = String.trim (String.sub trimmed i (String.length trimmed - i)) in
        match parse_formula formula_str with
        | None ->
          Printf.eprintf "  FAIL: parse error: %s %s\n" name formula_str;
          incr fail
        | Some formula ->
          let but_content = Pp2lp.Gen_but.gen_but ~name formula in
          let but_file = Filename.concat !out_dir (name ^ ".but") in
          let oc = open_out but_file in
          output_string oc but_content;
          close_out oc;
          incr ok
    end
  done with End_of_file -> ());
  close_in ic;
  Printf.printf "%d goals written to %s (%d failed)\n" !ok !out_dir !fail

let () =

  if Array.length Sys.argv < 2 then begin
    usage (); exit 1
  end;
  match Sys.argv.(1) with
  | "emit" -> cmd_emit ()
  | "check" -> cmd_check ()
  | "batch" -> cmd_batch ()
  | "parse" -> cmd_parse ()
  | "prove" -> cmd_prove ()
  | "synth" -> cmd_synth ()
  | "--help" | "-help" | "-h" -> usage ()
  | s ->
    Printf.eprintf "Unknown command: %s\n" s;
    usage ();
    exit 1
