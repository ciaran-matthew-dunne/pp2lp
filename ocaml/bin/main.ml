let usage () =
  Printf.eprintf "Usage: pp2lp <command> [options] [files...]\n\n";
  Printf.eprintf "Commands:\n";
  Printf.eprintf "  emit  FILE...   Emit Lambdapi .lp to stdout\n";
  Printf.eprintf "  check FILE...   Emit .lp + run lambdapi check\n";
  Printf.eprintf "  batch DIR       Batch check all .replay files in DIR\n";
  Printf.eprintf "  parse FILE...   Parse replay files (diagnostics only)\n"

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

let () =
  Pp2lp.Rule_db.auto_init ();
  if Array.length Sys.argv < 2 then begin
    usage (); exit 1
  end;
  match Sys.argv.(1) with
  | "emit" -> cmd_emit ()
  | "check" -> cmd_check ()
  | "batch" -> cmd_batch ()
  | "parse" -> cmd_parse ()
  | "--help" | "-help" | "-h" -> usage ()
  | s ->
    Printf.eprintf "Unknown command: %s\n" s;
    usage ();
    exit 1
