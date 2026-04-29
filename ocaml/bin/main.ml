(* pp2lp CLI entry point. Subcommands are dispatched on Sys.argv.(1).
   Each command parses its own arg vector with Arg.parse_argv. *)

(* ---- shared helpers ---- *)

let die fmt = Printf.ksprintf (fun s ->
  prerr_string s; prerr_newline (); exit 1) fmt

let getenv_opt s = try Some (Sys.getenv s) with Not_found -> None

(* Resolve the path to the running pp2lp binary. Used as part of the
   cache sentinel — when the binary changes, every cached pass is
   considered stale. *)
let pp2lp_binary () = Sys.executable_name

let lp_dir () =
  match getenv_opt "PP2LP_ROOT" with
  | Some r -> Filename.concat r "lp"
  | None -> "lp"

(* Drop all *.lpo compilation outputs under lp/. Used by `check --fresh`
   and `clean --lpo` / `clean --all`. *)
let drop_lpo_files () =
  let rec walk dir =
    try
      let dh = Unix.opendir dir in
      (try while true do
        let n = Unix.readdir dh in
        if n <> "." && n <> ".." then begin
          let p = Filename.concat dir n in
          match (try Some (Unix.stat p).Unix.st_kind with _ -> None) with
          | Some Unix.S_DIR -> walk p
          | Some Unix.S_REG when Filename.check_suffix n ".lpo" ->
            (try Unix.unlink p with _ -> ())
          | _ -> ()
        end
      done with End_of_file -> ());
      Unix.closedir dh
    with Unix.Unix_error _ -> ()
  in
  walk (lp_dir ())

(* Common cache config builder. *)
let make_cache_cfg suite ~xfail =
  let sentinel =
    Pp2lp.Cache.compute_sentinel
      ~bin_path:(pp2lp_binary ())
      ~lp_dir:(lp_dir ())
  in
  { Pp2lp.Runner.suite; xfail; sentinel }

(* ---- emit ---- *)

let cmd_emit () =
  let files = ref [] in
  let json = ref false in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "-debug",     Arg.Set Pp2lp.Proof_tree.debug,
        " Show proof tree debug output";
      "-debug-ins", Arg.Set Pp2lp.Ins.debug_ctx,
        " Dump hyp context on INS failure";
      "-trace",     Arg.Set Pp2lp.Emit_lp.trace,
        " Log emit-dispatch decisions to stderr (one line per case)";
      "--json",     Arg.Set json,
        " Emit one NDJSON record per file: {ok,file,lp,trust_count,admit_count,traces?}"
    ]
    (fun f -> files := f :: !files)
    "Usage: pp2lp emit [-debug] [-debug-ins] [-trace] [--json] file1.replay ...";
  let files = List.rev !files in
  if !json then begin
    List.iter (fun fp ->
      Pp2lp.Emit_lp.trace_file := fp;
      let ((kind, payload), traces) =
        Pp2lp.Emit_lp.with_trace_capture (fun () ->
          try
            let content = Pp2lp.Reconstruct.reconstruct_symbol fp in
            let body = Pp2lp.Emit_lp.lp_header ^ "\n" ^ content ^ "\n" in
            (`Ok, body)
          with
          | Pp2lp.Proof_tree.Ill_formed_replay msg -> (`Skip, msg)
          | Pp2lp.Proof_tree.Emit_admit msg -> (`Error, msg)
          | exn -> (`Error, Printexc.to_string exn))
      in
      let traces_json = Pp2lp.Json_out.JList (
        List.map (fun e ->
          Pp2lp.Json_out.JObj [
            "tag", Pp2lp.Json_out.JStr e.Pp2lp.Emit_lp.tag;
            "details", Pp2lp.Json_out.JStr e.Pp2lp.Emit_lp.details;
          ]) traces)
      in
      let trust_count, admit_count =
        match kind with
        | `Ok -> (Pp2lp.Runner.count_word "trust" payload,
                  Pp2lp.Runner.count_word "admit" payload)
        | _ -> (0, 0)
      in
      let ok = (kind = `Ok) in
      let kind_str = match kind with
        | `Ok -> "ok"
        | `Skip -> "skip"
        | `Error -> "error"
      in
      let fields = [
        "ok",          Pp2lp.Json_out.JBool ok;
        "kind",        Pp2lp.Json_out.JStr kind_str;
        "file",        Pp2lp.Json_out.JStr fp;
        "lp",          Pp2lp.Json_out.JStr (if ok then payload else "");
        "trust_count", Pp2lp.Json_out.JInt trust_count;
        "admit_count", Pp2lp.Json_out.JInt admit_count;
        "traces",      traces_json;
      ] in
      let fields =
        if not ok then fields @ ["error", Pp2lp.Json_out.JStr payload]
        else fields
      in
      Pp2lp.Json_out.print_line (Pp2lp.Json_out.JObj fields)
    ) files
  end else begin
    print_string Pp2lp.Emit_lp.lp_header;
    print_char '\n';
    List.iter (fun fp ->
      Pp2lp.Emit_lp.trace_file := fp;
      try
        let content = Pp2lp.Reconstruct.reconstruct_symbol fp in
        print_string content;
        print_char '\n'
      with
      | Pp2lp.Proof_tree.Ill_formed_replay msg ->
        Printf.eprintf "ill-formed replay: %s\n" msg;
        exit 2
      | Pp2lp.Proof_tree.Emit_admit msg ->
        Printf.eprintf "emit error: %s\n" msg;
        exit 3
      | exn ->
        Printf.eprintf "ERROR: %s: %s\n" fp (Printexc.to_string exn)
    ) files
  end

(* ---- parse ---- *)

let cmd_parse () =
  let files = ref [] in
  let verbose = ref false in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "-v", Arg.Set verbose, " Verbose output" ]
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
    end) files;
  Printf.printf "\nResults: %d ok, %d failed, %d total\n"
    !ok !fail (!ok + !fail)

(* ---- prove ---- *)

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
    [ "--name", Arg.Set_string name,
        " Symbol name for the proof (default: pp2lp_query)" ]
    (fun s -> formula_str := s)
    "Usage: pp2lp prove [--name NAME] FORMULA";
  if !formula_str = "" then
    die "Error: prove requires a formula argument\n\
         Example: pp2lp prove '(p and q) => (q and p)'";
  match parse_formula !formula_str with
  | None ->
    die "Error: failed to parse formula: %s" !formula_str
  | Some formula ->
    (try
      let output = Pp2lp.Gen_but.prove ~name:!name formula in
      print_string output
    with Failure msg -> die "Error: %s" msg)

(* ---- synth ---- *)

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
  if !goals_file = "" || !out_dir = "" then
    die "Usage: pp2lp synth GOALS_FILE OUTPUT_DIR";
  (try Unix.mkdir !out_dir 0o755 with Unix.Unix_error _ -> ());
  let ic = open_in !goals_file in
  let ok = ref 0 in
  let fail = ref 0 in
  (try while true do
    let line = input_line ic in
    let trimmed = String.trim line in
    if trimmed = "" || trimmed.[0] = '#' then ()
    else begin
      match String.index_opt trimmed ' ' with
      | None ->
        Printf.eprintf "  SKIP: no formula after name: %s\n" trimmed;
        incr fail
      | Some i ->
        let name = String.sub trimmed 0 i in
        let formula_str =
          String.trim (String.sub trimmed i (String.length trimmed - i)) in
        match parse_formula formula_str with
        | None ->
          Printf.eprintf "  FAIL: parse error: %s %s\n" name formula_str;
          incr fail
        | Some formula ->
          let but_content = Pp2lp.Gen_but.gen_but ~name formula in
          let but_file = Filename.concat !out_dir (name ^ ".but") in
          let changed = try
            let ic2 = open_in but_file in
            let old = In_channel.input_all ic2 in
            close_in ic2;
            old <> but_content
          with Sys_error _ -> true in
          if changed then begin
            let oc = open_out but_file in
            output_string oc but_content;
            close_out oc
          end;
          incr ok
    end
  done with End_of_file -> ());
  close_in ic;
  Printf.printf "%d goals written to %s (%d failed)\n" !ok !out_dir !fail

(* ---- check ---- *)

let parse_suite_arg s =
  if not (Pp2lp.Suite.exists s) then
    die "Unknown suite %S (known: %s)" s
      (String.concat ", " (Pp2lp.Suite.names ()));
  Pp2lp.Suite.find s

let format_outcome_summary stats =
  let pass, fail, skip, cached, trust, admit = stats in
  let parts = ref [] in
  parts := Printf.sprintf "%d passed, %d failed" pass fail :: !parts;
  if skip > 0 then parts := Printf.sprintf "%d gen-fail" skip :: !parts;
  let main = String.concat ", " (List.rev !parts) in
  let main =
    if cached > 0 then Printf.sprintf "%s (%d cached)" main cached
    else main
  in
  let warn_parts = ref [] in
  if trust > 0 then warn_parts := Printf.sprintf "%d trust" trust :: !warn_parts;
  if admit > 0 then warn_parts := Printf.sprintf "%d admit" admit :: !warn_parts;
  let main =
    match List.rev !warn_parts with
    | [] -> main
    | xs -> Printf.sprintf "%s [%s]" main (String.concat ", " xs)
  in
  main

let cmd_check () =
  let suite_name = ref "prv" in
  let job = ref "" in
  let name = ref "" in
  let fresh = ref false in
  let all_failures = ref false in
  let json = ref false in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "--suite", Arg.Set_string suite_name,
        " Benchmark suite (default: prv)";
      "--job",   Arg.Set_string job,
        " Filter tests by name prefix";
      "--name",  Arg.Set_string name,
        " Run a single test (bypasses cache)";
      "--fresh", Arg.Set fresh,
        " Drop cache + .lpo files before running";
      "--all-failures", Arg.Set all_failures,
        " Report all failures instead of fast-fail";
      "--all", Arg.Set all_failures,
        " Alias for --all-failures";
      "--json",  Arg.Set json,
        " Emit one NDJSON record per test, plus a summary record at end"
    ]
    (fun s ->
      die "check: unexpected positional arg %S (use --name=%s)" s s)
    "Usage: pp2lp check [--suite=X] [--name=Y] [--job=PFX] [--fresh] \
                       [--all-failures] [--json]";
  let suite = parse_suite_arg !suite_name in
  let suite_dir = Pp2lp.Suite.dir suite in
  if !fresh then begin
    Pp2lp.Cache.clear_all suite_dir;
    drop_lpo_files ()
  end;
  let cfg = make_cache_cfg suite ~xfail:[] in
  Pp2lp.Runner.ensure_pkg suite;
  let all_tests = Pp2lp.Runner.list_tests suite in
  let tests =
    if !name <> "" then begin
      if not (List.mem !name all_tests) then
        die "No replay for %S in suite %s" !name suite.Pp2lp.Suite.name;
      [!name]
    end else if !job <> "" then
      List.filter (String.starts_with ~prefix:!job) all_tests
    else all_tests
  in
  if tests = [] then
    die "No replay files in %s — run 'pp2lp gen --suite=%s' first"
      suite_dir suite.Pp2lp.Suite.name;
  let force = !name <> "" in
  let t0 = Unix.gettimeofday () in
  let pass = ref 0 in
  let fail = ref 0 in
  let skip = ref 0 in
  let cached = ref 0 in
  let tot_trust = ref 0 in
  let tot_admit = ref 0 in
  let early_exit = ref None in
  let fast_fail = not !all_failures && !name = "" in
  let report_outcome n out =
    if !json then begin
      let j_kind, fields =
        match out with
        | Pp2lp.Runner.Pass { trust; admit; cached } ->
          "pass", [
            "trust", Pp2lp.Json_out.JInt trust;
            "admit", Pp2lp.Json_out.JInt admit;
            "cached", Pp2lp.Json_out.JBool cached;
          ]
        | Pp2lp.Runner.Skipped { reason; cached } ->
          "skip", [
            "reason", Pp2lp.Json_out.JStr reason;
            "cached", Pp2lp.Json_out.JBool cached;
          ]
        | Pp2lp.Runner.Failed { detail; cached } ->
          "fail", [
            "detail", Pp2lp.Json_out.JStr detail;
            "cached", Pp2lp.Json_out.JBool cached;
          ]
      in
      Pp2lp.Json_out.print_line (Pp2lp.Json_out.JObj (
        ("kind", Pp2lp.Json_out.JStr j_kind) ::
        ("name", Pp2lp.Json_out.JStr n) ::
        ("suite", Pp2lp.Json_out.JStr suite.Pp2lp.Suite.name) ::
        fields))
    end else begin
      let single = (!name <> "") in
      match out with
      | Pp2lp.Runner.Pass { trust; admit; cached = c } ->
        if single then begin
          Printf.printf "OK %s\n" n;
          if trust > 0 then Printf.printf "  %d trust\n" trust;
          if admit > 0 then Printf.printf "  %d admit\n" admit
        end else if not c && (trust > 0 || admit > 0) then begin
          let ws = ref [] in
          if trust > 0 then ws := Printf.sprintf "%d trust" trust :: !ws;
          if admit > 0 then ws := Printf.sprintf "%d admit" admit :: !ws;
          Printf.printf "  warn %s: %s\n" n
            (String.concat ", " (List.rev !ws))
        end
      | Pp2lp.Runner.Skipped { reason; cached = c } ->
        if single || not c then Printf.printf "SKIP %s: %s\n" n reason
      | Pp2lp.Runner.Failed { detail; cached = c } ->
        if c && not single then Printf.printf "FAIL %s (cached)\n" n
        else begin
          Printf.printf "FAIL %s\n" n;
          let formatted = Pp2lp.Lp_diag.format_for_terminal detail in
          if String.trim formatted <> "" then print_string formatted
        end
    end
  in
  let summarise () =
    if !name <> "" && not !json then ()
    else if !json then begin
      let dur = int_of_float (Unix.gettimeofday () -. t0) in
      Pp2lp.Json_out.print_line (Pp2lp.Json_out.JObj [
        "kind",    Pp2lp.Json_out.JStr "summary";
        "suite",   Pp2lp.Json_out.JStr suite.Pp2lp.Suite.name;
        "passed",  Pp2lp.Json_out.JInt !pass;
        "failed",  Pp2lp.Json_out.JInt !fail;
        "skipped", Pp2lp.Json_out.JInt !skip;
        "cached",  Pp2lp.Json_out.JInt !cached;
        "trust",   Pp2lp.Json_out.JInt !tot_trust;
        "admit",   Pp2lp.Json_out.JInt !tot_admit;
        "duration_seconds", Pp2lp.Json_out.JInt dur;
      ])
    end else begin
      let dur = int_of_float (Unix.gettimeofday () -. t0) in
      let stats = (!pass, !fail, !skip, !cached, !tot_trust, !tot_admit) in
      Printf.printf "%s (%ds)\n" (format_outcome_summary stats) dur
    end
  in
  (try
    List.iter (fun n ->
      let out = Pp2lp.Runner.run_one ~cfg ~force n in
      (match out with
       | Pp2lp.Runner.Pass { trust; admit; cached = c } ->
         incr pass; if c then incr cached;
         tot_trust := !tot_trust + trust;
         tot_admit := !tot_admit + admit
       | Pp2lp.Runner.Skipped { cached = c; _ } ->
         incr skip; if c then incr cached
       | Pp2lp.Runner.Failed { cached = c; _ } ->
         incr fail; if c then incr cached);
      report_outcome n out;
      (match out with
       | Pp2lp.Runner.Failed _ when fast_fail ->
         early_exit := Some 1; raise Exit
       | _ -> ())
    ) tests
  with Exit -> ());
  summarise ();
  match !early_exit with
  | Some n -> exit n
  | None -> if !fail > 0 then exit 1

(* ---- status ---- *)

let cmd_status () =
  let only = ref None in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "--suite", Arg.String (fun s -> only := Some s),
        " Show only the named suite" ]
    (fun s -> die "status: unexpected positional arg %S" s)
    "Usage: pp2lp status [--suite=X]";
  print_endline "=== pp2lp status ===";
  List.iter (fun (s : Pp2lp.Suite.t) ->
    if (match !only with None -> true | Some n -> n = s.name) then begin
      let dir = Pp2lp.Suite.dir s in
      if not (Pp2lp.Cache.exists dir) then ()
      else begin
        let replays = Pp2lp.Runner.list_tests s in
        if replays = [] then ()
        else begin
          let markers = Pp2lp.Cache.list_markers dir in
          let pass = List.length (List.filter (fun (_, k) -> k = Pp2lp.Cache.Ok) markers) in
          let fail = List.length (List.filter (fun (_, k) -> k = Pp2lp.Cache.Fail) markers) in
          let skip_markers = List.filter (fun (_, k) -> k = Pp2lp.Cache.Skip) markers in
          let known = pass + fail + List.length skip_markers in
          let stale = List.length replays - known in
          let main = Printf.sprintf "Suite %s: %d replays | %d pass, %d fail"
                       s.name (List.length replays) pass fail
          in
          let main = if stale > 0 then Printf.sprintf "%s, %d stale" main stale else main in
          (* Skips are emit-time detection of upstream replay damage — fold
             into gen-fail so they're counted alongside PP-side failures. *)
          let classify_skip body =
            let body = String.trim body in
            let contains sub s =
              let nlen = String.length sub in
              let slen = String.length s in
              let rec aux i =
                if i + nlen > slen then false
                else if String.sub s i nlen = sub then true
                else aux (i + 1)
              in
              aux 0
            in
            if contains "at end of replay" body then ("fail-replay", "truncated")
            else ("fail-emit", body)
          in
          let skip_fails =
            List.filter_map (fun (n, _) ->
              match Pp2lp.Cache.read_marker_body ~suite_dir:dir ~name:n Pp2lp.Cache.Skip with
              | Some body -> Some (classify_skip body)
              | None -> None
            ) skip_markers
          in
          let gen_status_path = Filename.concat dir ".gen_status.tsv" in
          let gen_fails =
            if not (Pp2lp.Cache.exists gen_status_path) then skip_fails
            else begin
              let ic = open_in gen_status_path in
              let acc = ref skip_fails in
              (try while true do
                let l = input_line ic in
                match String.split_on_char '\t' l with
                | _ :: stage :: reason :: _
                  when String.starts_with ~prefix:"fail-" stage ->
                  acc := (stage, reason) :: !acc
                | _ -> ()
              done with End_of_file -> ());
              close_in ic;
              !acc
            end
          in
          let main =
            if gen_fails <> []
            then Printf.sprintf "%s | %d gen-fail" main (List.length gen_fails)
            else main
          in
          print_endline main;
          (* Group gen_fails by (stage, reason) *)
          if gen_fails <> [] then begin
            let groups = Hashtbl.create 8 in
            List.iter (fun (st, rsn) ->
              let key = st ^ "\t" ^ rsn in
              let n = try Hashtbl.find groups key with Not_found -> 0 in
              Hashtbl.replace groups key (n + 1)) gen_fails;
            let entries =
              Hashtbl.fold (fun k n acc -> (k, n) :: acc) groups []
              |> List.sort compare
            in
            List.iter (fun (k, n) ->
              match String.split_on_char '\t' k with
              | [st; rsn] ->
                Printf.printf "    %3d  %s %s\n" n st rsn
              | _ -> ()) entries
          end
        end
      end
    end
  ) Pp2lp.Suite.all

(* ---- coverage ---- *)

let cmd_coverage () =
  let by_suite = ref false in
  let missing = ref false in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "--by-suite", Arg.Set by_suite, " Per-suite × per-rule matrix";
      "--missing",  Arg.Set missing,  " Show only rules with zero coverage" ]
    (fun s -> die "coverage: unexpected positional arg %S" s)
    "Usage: pp2lp coverage [--by-suite] [--missing]";
  if !by_suite
  then Pp2lp.Coverage.print_by_suite ~missing:!missing ()
  else Pp2lp.Coverage.print_simple ~missing:!missing ()

(* ---- clean ---- *)

let cmd_clean () =
  let lpo = ref false in
  let cache = ref false in
  let all = ref false in
  let suite_name = ref "" in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "--lpo",   Arg.Set lpo,   " Drop lp/**/*.lpo files";
      "--cache", Arg.Set cache, " Drop bench/<suite>/.cache/ markers";
      "--all",   Arg.Set all,   " Full reset (cache + .lpo + outputs)";
      "--suite", Arg.Set_string suite_name,
        " Restrict --cache to one suite" ]
    (fun s -> die "clean: unexpected positional arg %S" s)
    "Usage: pp2lp clean [--lpo] [--cache] [--all] [--suite=X]";
  if not (!lpo || !cache || !all) then
    die "clean: pick at least one of --lpo, --cache, --all";
  if !lpo then drop_lpo_files ();
  if !cache then begin
    let suites =
      if !suite_name = "" then Pp2lp.Suite.all
      else [parse_suite_arg !suite_name]
    in
    List.iter (fun s -> Pp2lp.Cache.clear_all (Pp2lp.Suite.dir s)) suites
  end;
  if !all then begin
    drop_lpo_files ();
    List.iter (fun s -> Pp2lp.Cache.clear_all (Pp2lp.Suite.dir s)) Pp2lp.Suite.all;
    let _ = Sys.command "cd ocaml && dune clean" in
    ()
  end

(* ---- gen ---- *)

let cmd_gen () =
  let suite_name = ref "prv" in
  let alloc = ref None in
  let all = ref false in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "--suite", Arg.Set_string suite_name, " Suite to generate";
      "--alloc", Arg.String (fun s -> alloc := Some s),
        " Override krt -a allocator string";
      "--all",   Arg.Set all,
        " Regenerate all four active suites" ]
    (fun s -> die "gen: unexpected positional arg %S" s)
    "Usage: pp2lp gen [--suite=X] [--alloc=...] [--all]";
  let run_one (suite : Pp2lp.Suite.t) =
    let dir = Pp2lp.Suite.dir suite in
    (try Unix.mkdir dir 0o755 with Unix.Unix_error _ -> ());
    if suite.synth then begin
      let goals = Filename.concat dir "goals.txt" in
      if not (Pp2lp.Cache.exists goals) then
        die "synth suite %s: missing %s" suite.name goals;
      let argv = [| Sys.executable_name; "synth"; goals; dir |] in
      let pid = Unix.create_process argv.(0) argv
                  Unix.stdin Unix.stdout Unix.stderr in
      let _, status = Unix.waitpid [] pid in
      match status with
      | Unix.WEXITED 0 -> ()
      | _ -> die "synth failed for suite %s" suite.name
    end;
    if suite.name = "og" then begin
      print_endline "og suite has no .but sources; nothing to regenerate"
    end else begin
      let alloc_arg = match !alloc with
        | Some s -> s
        | None -> suite.alloc
      in
      let argv = Array.of_list [
        "python3"; "bench/gen_traces.py"; "-q";
        "--alloc"; alloc_arg;
        "-o"; dir; dir
      ] in
      let pid = Unix.create_process argv.(0) argv
                  Unix.stdin Unix.stdout Unix.stderr in
      let _, status = Unix.waitpid [] pid in
      match status with
      | Unix.WEXITED 0 -> ()
      | _ -> die "gen_traces.py failed for suite %s" suite.name
    end
  in
  if !all then
    List.iter run_one
      (List.filter (fun (s : Pp2lp.Suite.t) -> s.name <> "fuzz")
         Pp2lp.Suite.all)
  else
    run_one (parse_suite_arg !suite_name)

(* ---- debug ---- *)

let cmd_debug () =
  let show = ref "both" in
  let replay = ref "" in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "--show", Arg.Set_string show,
        " dispatch | tree | both (default: both)" ]
    (fun s -> if !replay = "" then replay := s
              else die "debug: extra positional arg %S" s)
    "Usage: pp2lp debug REPLAY [--show=dispatch|tree|both]";
  if !replay = "" then die "Usage: pp2lp debug REPLAY [--show=...]";
  let want_dispatch = !show = "dispatch" || !show = "both" in
  let want_tree = !show = "tree" || !show = "both" in
  if want_tree then begin
    print_endline "=== Proof tree (PP rule sequence) ===";
    let lines = Pp2lp.Parse_pp.parse_pp_replay !replay in
    List.iter (fun ((rule, arg), _rhs) ->
      let arg_str = match arg with
        | None -> ""
        | Some _ -> "(…)"
      in
      Printf.printf "  %s%s\n" rule arg_str) lines
  end;
  if want_dispatch then begin
    if want_tree then print_endline "";
    print_endline "=== Emitter dispatch trace ===";
    Pp2lp.Emit_lp.trace_file := !replay;
    let ((kind, payload), traces) =
      Pp2lp.Emit_lp.with_trace_capture (fun () ->
        try
          let body = Pp2lp.Reconstruct.reconstruct_symbol !replay in
          (`Ok, body)
        with
        | Pp2lp.Proof_tree.Ill_formed_replay msg -> (`Skip, msg)
        | Pp2lp.Proof_tree.Emit_admit msg -> (`Error, msg)
        | exn -> (`Error, Printexc.to_string exn))
    in
    if traces = [] then
      print_endline "  (no special-case dispatches)"
    else
      List.iter (fun e ->
        Printf.printf "  %s%s\n" e.Pp2lp.Emit_lp.tag
          (if e.details = "" then "" else "  " ^ e.details)
      ) traces;
    (match kind with
     | `Skip ->
       Printf.printf "\n[ill-formed replay: %s]\n" payload;
       exit 2
     | `Error ->
       Printf.printf "\n[emit error: %s]\n" payload;
       exit 3
     | `Ok -> ())
  end

(* ---- show-fail ---- *)

let cmd_show_fail () =
  let suite_name = ref "" in
  let name = ref "" in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  let pos = ref 0 in
  Arg.parse_argv argv []
    (fun s ->
      match !pos with
      | 0 -> suite_name := s; incr pos
      | 1 -> name := s; incr pos
      | _ -> die "show-fail: too many positional args")
    "Usage: pp2lp show-fail SUITE NAME";
  if !suite_name = "" || !name = "" then
    die "Usage: pp2lp show-fail SUITE NAME";
  let suite = parse_suite_arg !suite_name in
  let suite_dir = Pp2lp.Suite.dir suite in
  let body =
    Pp2lp.Cache.read_marker_body ~suite_dir ~name:!name Pp2lp.Cache.Fail
  in
  match body with
  | None ->
    let body_skip =
      Pp2lp.Cache.read_marker_body ~suite_dir ~name:!name Pp2lp.Cache.Skip in
    (match body_skip with
     | Some s ->
       Printf.printf "(no .fail; .skip says: %s)\n" (String.trim s);
       exit 0
     | None ->
       Printf.printf "No .fail marker for %s in suite %s\n"
         !name suite.name;
       exit 1)
  | Some text ->
    Printf.printf "=== %s/%s.fail ===\n" suite.name !name;
    let formatted = Pp2lp.Lp_diag.format_for_terminal text in
    if String.trim formatted <> "" then print_string formatted;
    let lp_path = Filename.concat suite_dir (!name ^ ".lp") in
    if Pp2lp.Cache.exists lp_path then begin
      let diags, _ = Pp2lp.Lp_diag.parse_ndjson text in
      let errors = List.filter (fun d -> d.Pp2lp.Lp_diag.severity = "error") diags in
      List.iter (fun d ->
        match d.Pp2lp.Lp_diag.loc with
        | Some loc ->
          Printf.printf "\n--- %s:%d (±3 lines) ---\n" loc.file loc.line;
          (try
            let ic = open_in lp_path in
            let line_num = ref 0 in
            (try while true do
              let l = input_line ic in
              incr line_num;
              if !line_num >= loc.line - 3 && !line_num <= loc.line + 3 then
                Printf.printf "%s%4d  %s\n"
                  (if !line_num = loc.line then "→ " else "  ")
                  !line_num l
            done with End_of_file -> ());
            close_in ic
          with _ -> ())
        | None -> ()
      ) errors
    end

(* ---- diff ---- *)

let cmd_diff () =
  let replay = ref "" in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv []
    (fun s -> if !replay = "" then replay := s
              else die "diff: extra positional arg %S" s)
    "Usage: pp2lp diff REPLAY";
  if !replay = "" then die "Usage: pp2lp diff REPLAY";
  let pp_lines = Pp2lp.Parse_pp.parse_pp_replay !replay in
  Pp2lp.Emit_lp.trace_file := !replay;
  let lp_text =
    try Pp2lp.Reconstruct.reconstruct_symbol !replay
    with
    | Pp2lp.Proof_tree.Ill_formed_replay msg -> "(ill-formed replay: " ^ msg ^ ")"
    | Pp2lp.Proof_tree.Emit_admit msg -> "(emit error: " ^ msg ^ ")"
    | exn -> "(exception: " ^ Printexc.to_string exn ^ ")"
  in
  let lp_lines = String.split_on_char '\n' lp_text in
  let max_pp = List.length pp_lines in
  let max_lp = List.length lp_lines in
  let nrows = max max_pp max_lp in
  Printf.printf "%-40s | %s\n" "PP RULE" "LP";
  Printf.printf "%-40s-+-%s\n"
    (String.make 40 '-')
    (String.make 38 '-');
  let rec range a b = if a >= b then [] else a :: range (a + 1) b in
  List.iter (fun i ->
    let pp =
      if i < max_pp then
        let ((rule, arg), _) = List.nth pp_lines i in
        rule ^ (match arg with None -> "" | Some _ -> "(…)")
      else ""
    in
    let lp = if i < max_lp then List.nth lp_lines i else "" in
    let pp_short = if String.length pp > 40 then
        String.sub pp 0 37 ^ "..." else pp in
    let lp_short = if String.length lp > 80 then
        String.sub lp 0 77 ^ "..." else lp in
    Printf.printf "%-40s | %s\n" pp_short lp_short
  ) (range 0 nrows)

(* ---- lp-check ---- *)

(* Run lambdapi check on one path. Returns (rc, output). *)
let lp_check_one ~json path =
  let argv =
    if json && Pp2lp.Runner.detect_lambdapi_json ()
    then [| "lambdapi"; "check"; "--json"; "-c"; path |]
    else [| "lambdapi"; "check"; "-c"; path |]
  in
  let rc, out, err = Pp2lp.Runner.run_capture argv in
  (rc, out ^ err)

let cmd_lp_check () =
  let json = ref false in
  let all_errors = ref false in
  let files = ref [] in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "--json", Arg.Set json,
        " Emit one NDJSON record per file: {ok, file, errors[]}";
      "--all-errors", Arg.Set all_errors,
        " Show all errors (default: only the first)" ]
    (fun s -> files := s :: !files)
    "Usage: pp2lp lp-check [--json] [--all-errors] FILE...";
  let files = List.rev !files in
  if files = [] then die "lp-check: at least one FILE required";
  let any_fail = ref false in
  List.iter (fun f ->
    let rc, output = lp_check_one ~json:true f in
    let diags, _raw = Pp2lp.Lp_diag.parse_ndjson output in
    let errors = List.filter
      (fun d -> d.Pp2lp.Lp_diag.severity = "error") diags in
    let errors = if !all_errors then errors
                 else (match errors with [] -> [] | x :: _ -> [x]) in
    let ok = (rc = 0) in
    if not ok then any_fail := true;
    if !json then begin
      let errs_json = Pp2lp.Json_out.JList
        (List.map Pp2lp.Lp_diag.diag_to_json errors) in
      Pp2lp.Json_out.print_line (Pp2lp.Json_out.JObj [
        "kind",   Pp2lp.Json_out.JStr "lp-check";
        "file",   Pp2lp.Json_out.JStr f;
        "ok",     Pp2lp.Json_out.JBool ok;
        "exit_code", Pp2lp.Json_out.JInt rc;
        "errors", errs_json;
      ])
    end else begin
      if ok then Printf.printf "OK %s\n" f
      else begin
        Printf.printf "FAIL %s\n" f;
        let formatted = Pp2lp.Lp_diag.format_for_terminal output in
        if String.trim formatted <> "" then print_string formatted
      end
    end
  ) files;
  if !any_fail then exit 1

(* ---- lp-axioms ---- *)

let cmd_lp_axioms () =
  let scope = ref "file" in
  let json = ref false in
  let files = ref [] in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "--scope", Arg.Set_string scope,
        " file (default) | project (follow `require` within project)";
      "--json", Arg.Set json,
        " Emit a single JSON record" ]
    (fun s -> files := s :: !files)
    "Usage: pp2lp lp-axioms [--scope=file|project] [--json] FILE...";
  let files = List.rev !files in
  if files = [] then die "lp-axioms: at least one FILE required";
  let scope = !scope in
  if scope <> "file" && scope <> "project" then
    die "lp-axioms: --scope must be 'file' or 'project' (got %S)" scope;
  let assumptions = ref [] in
  let rules = ref [] in
  let admits = ref [] in
  let scanned = Hashtbl.create 16 in
  let unresolved = Hashtbl.create 4 in
  let rec scan_one ~origin path =
    let p = try Unix.realpath path with _ -> path in
    if Hashtbl.mem scanned p then ()
    else begin
      Hashtbl.replace scanned p ();
      if not (Pp2lp.Cache.exists p) then begin
        Hashtbl.replace unresolved (path ^ "  (from: " ^ origin ^ ")") ()
      end else begin
        let a, r, d = Pp2lp.Lp_tools.scan_file p in
        assumptions := !assumptions @ a;
        rules := !rules @ r;
        admits := !admits @ d;
        if scope = "project" then begin
          let raw = Pp2lp.Lp_tools.read_file_text p in
          let stripped = Pp2lp.Lp_tools.strip_comments raw in
          let stmts = Pp2lp.Lp_tools.split_statements stripped in
          let roots = Pp2lp.Lp_tools.discover_pkg_roots
                        ~extra_dirs:[Sys.getcwd ()] files in
          List.iter (fun (_, s) ->
            let mods = Pp2lp.Lp_tools.parse_requires s in
            List.iter (fun m ->
              match Pp2lp.Lp_tools.resolve_module ~roots m with
              | Some path -> scan_one ~origin:p path
              | None -> Hashtbl.replace unresolved (m ^ "  (from: " ^ p ^ ")") ()
            ) mods
          ) stmts
        end
      end
    end
  in
  List.iter (fun f -> scan_one ~origin:"<cli>" f) files;
  let assumptions = !assumptions in
  let rules = !rules in
  let admits = !admits in
  (* defined_by_rules: non-propositional symbols that head a rule *)
  let rule_heads = Hashtbl.create 32 in
  List.iter (fun r ->
    if r.Pp2lp.Lp_tools.symbol <> ""
    then Hashtbl.replace rule_heads r.Pp2lp.Lp_tools.symbol ()) rules;
  let defined_by_rules, pure_assumptions =
    List.partition (fun a ->
      Hashtbl.mem rule_heads a.Pp2lp.Lp_tools.name
      && not a.propositional) assumptions
  in
  if !json then begin
    let assum_to_json a =
      Pp2lp.Json_out.JObj [
        "file", Pp2lp.Json_out.JStr a.Pp2lp.Lp_tools.a_file;
        "line", Pp2lp.Json_out.JInt a.a_line;
        "name", Pp2lp.Json_out.JStr a.name;
        "type", Pp2lp.Json_out.JStr a.type_;
        "propositional", Pp2lp.Json_out.JBool a.propositional;
        "constant", Pp2lp.Json_out.JBool a.constant;
      ]
    in
    let rule_to_json r =
      Pp2lp.Json_out.JObj [
        "file", Pp2lp.Json_out.JStr r.Pp2lp.Lp_tools.r_file;
        "line", Pp2lp.Json_out.JInt r.r_line;
        "symbol", Pp2lp.Json_out.JStr r.symbol;
        "lhs", Pp2lp.Json_out.JStr r.lhs;
        "rhs", Pp2lp.Json_out.JStr r.rhs;
      ]
    in
    let admit_to_json d =
      Pp2lp.Json_out.JObj [
        "file", Pp2lp.Json_out.JStr d.Pp2lp.Lp_tools.d_file;
        "line", Pp2lp.Json_out.JInt d.d_line;
      ]
    in
    let unresolved_list =
      Hashtbl.fold (fun k _ acc -> Pp2lp.Json_out.JStr k :: acc) unresolved []
    in
    Pp2lp.Json_out.print_line (Pp2lp.Json_out.JObj [
      "kind", Pp2lp.Json_out.JStr "lp-axioms";
      "scope", Pp2lp.Json_out.JStr scope;
      "scanned_files", Pp2lp.Json_out.JInt (Hashtbl.length scanned);
      "assumptions",      Pp2lp.Json_out.JList (List.map assum_to_json pure_assumptions);
      "defined_by_rules", Pp2lp.Json_out.JList (List.map assum_to_json defined_by_rules);
      "rewrite_rules",    Pp2lp.Json_out.JList (List.map rule_to_json rules);
      "admits",           Pp2lp.Json_out.JList (List.map admit_to_json admits);
      "unresolved_imports", Pp2lp.Json_out.JList unresolved_list;
    ])
  end else begin
    Printf.printf "scope=%s, files scanned: %d\n"
      scope (Hashtbl.length scanned);
    Printf.printf "\n=== Assumptions (%d) ===\n" (List.length pure_assumptions);
    List.iter (fun a ->
      let kw = if a.Pp2lp.Lp_tools.constant then "constant " else "" in
      Printf.printf "  %s:%d  %ssymbol %s : %s%s\n"
        a.Pp2lp.Lp_tools.a_file a.a_line kw a.name a.type_
        (if a.propositional then "  [prop]" else "")
    ) pure_assumptions;
    if defined_by_rules <> [] then begin
      Printf.printf "\n=== Defined by rules (%d) ===\n"
        (List.length defined_by_rules);
      List.iter (fun a ->
        Printf.printf "  %s:%d  symbol %s : %s\n"
          a.Pp2lp.Lp_tools.a_file a.a_line a.name a.type_
      ) defined_by_rules
    end;
    if admits <> [] then begin
      Printf.printf "\n=== Admits (%d) ===\n" (List.length admits);
      List.iter (fun d ->
        Printf.printf "  %s:%d\n" d.Pp2lp.Lp_tools.d_file d.d_line
      ) admits
    end;
    Printf.printf "\nrewrite rules: %d\n" (List.length rules);
    let n_unres = Hashtbl.length unresolved in
    if n_unres > 0 then begin
      Printf.printf "\n=== Unresolved imports (%d) ===\n" n_unres;
      Hashtbl.iter (fun k () -> Printf.printf "  %s\n" k) unresolved
    end
  end

(* ---- lp-probe ---- *)

(* Insert a single command at LINE in FILE (sibling probe file in the
   same directory), run lambdapi check, slice the output to the
   command's location, return it. Reverts/cleans up on exit. *)
let cmd_lp_probe () =
  let file = ref "" in
  let line = ref 0 in
  let command = ref "" in
  let raw = ref false in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  let pos = ref 0 in
  Arg.parse_argv argv
    [ "--raw", Arg.Set raw,
        " Print full lambdapi output (no slicing)" ]
    (fun s ->
      match !pos with
      | 0 -> file := s; incr pos
      | 1 -> line := (try int_of_string s with _ ->
              die "lp-probe: LINE must be an integer (got %S)" s);
              incr pos
      | 2 -> command := s; incr pos
      | _ -> die "lp-probe: extra positional arg %S" s)
    "Usage: pp2lp lp-probe FILE LINE 'COMMAND;'\n\
     Inserts COMMAND at LINE of FILE (in a sibling probe file), runs\n\
     `lambdapi check`, slices the output to the command's location.\n\
     Examples:\n\
       pp2lp lp-probe lp/B.lp 50 'compute 𝟏 + 𝟏;'\n\
       pp2lp lp-probe lp/B.lp 50 'type bool_cases;'\n\
       pp2lp lp-probe lp/B.lp 50 'print BOOL;'\n\
     Inside a `begin … end` proof:\n\
       pp2lp lp-probe lp/Foo.lp 12 'print;'      (dump goal state)\n\
       pp2lp lp-probe lp/Foo.lp 12 'proofterm;'  (partial proof term)";
  if !file = "" || !pos < 3 then
    die "Usage: pp2lp lp-probe FILE LINE 'COMMAND;'";
  let probe, mapping =
    Pp2lp.Lp_tools.make_probe ~original:!file
      ~insertions:[ (!line, !command) ]
  in
  Fun.protect
    ~finally:(fun () -> Pp2lp.Lp_tools.cleanup_probe probe)
    (fun () ->
      let argv = [| "lambdapi"; "check"; probe |] in
      let rc, out, err = Pp2lp.Runner.run_capture argv in
      if !raw then
        print_string (out ^ err)
      else begin
        let probe_line = match mapping with
          | (l, _) :: _ -> l
          | [] -> !line
        in
        (* Probe output (compute / type / print of a symbol / in-proof
           print / proofterm) goes to stdout. Try to slice to the
           command's location; if no marker fires, return everything
           between Start/End checking. Errors live on stderr. *)
        let precise =
          Pp2lp.Lp_tools.slice_at_probe_line ~probe_path:probe
            ~probe_line out
        in
        let body =
          if precise <> "" then precise
          else Pp2lp.Lp_tools.between_session_markers out
        in
        if rc <> 0 then begin
          let formatted = Pp2lp.Lp_diag.format_for_terminal err in
          if String.trim formatted <> "" then print_string formatted
          else if String.trim err <> "" then print_string err
          else if String.trim body <> "" then print_endline body
          else print_endline "(probe failed; no output captured)"
        end else if String.trim body = "" then
          print_endline "(no output)"
        else
          print_endline body
      end;
      if rc <> 0 then exit rc)

(* ---- lp-debug ---- *)

(* Reshaped: instead of running `lambdapi check --debug=FLAGS` over the
   whole file, insert `debug +FLAGS;` and `debug -FLAGS;` into a sibling
   probe file at user-chosen lines, then slice the trace between them.
   Result: scoped debug output, bounded by construction. *)

let cmd_lp_debug () =
  let flags = ref "" in
  let at = ref 0 in
  let end_at = ref 0 in
  let save_to = ref "" in
  let raw = ref false in
  let file = ref "" in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "--flags",   Arg.Set_string flags,
        " Lambdapi debug flags (e.g. u, a, t, ut)";
      "--at",      Arg.Set_int at,
        " First line to trace (inclusive; default 1 = whole file)";
      "--end-at",  Arg.Set_int end_at,
        " Last line to trace (inclusive; default end-of-file)";
      "--save-to", Arg.Set_string save_to,
        " Write FULL raw lambdapi output to this path";
      "--raw",     Arg.Set raw,
        " Print full output (no slicing to between toggles)" ]
    (fun s -> if !file = "" then file := s
              else die "lp-debug: extra positional arg %S" s)
    "Usage: pp2lp lp-debug FILE --flags=FLAGS [--at=LINE] [--end-at=LINE]\n\
     Inserts `debug +FLAGS;` before line --at and `debug -FLAGS;` after\n\
     line --end-at in a sibling probe file (both bounds inclusive), then\n\
     runs `lambdapi check` and slices the trace between the toggles.\n\
     Examples:\n\
       pp2lp lp-debug lp/Foo.lp --flags=u                # whole file\n\
       pp2lp lp-debug lp/Foo.lp --flags=u --at=42        # line 42 to EOF\n\
       pp2lp lp-debug lp/Foo.lp --flags=u --at=42 --end-at=42  # just L42\n\
       pp2lp lp-debug lp/Foo.lp --flags=u --at=42 --end-at=65";
  if !file = "" then die "lp-debug: FILE required";
  if !flags = "" then die "lp-debug: --flags required";
  String.iter (fun c ->
    if not ((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9'))
    then die "lp-debug: invalid char %C in --flags" c) !flags;
  let line_count =
    let lines = Pp2lp.Lp_tools.read_lines !file in
    List.length lines
  in
  let at = if !at = 0 then 1 else !at in
  (* --end-at is inclusive: insert the off-toggle AFTER the named line,
     i.e. at probe position end_at + 1, so [at..end_at] is fully traced.
     Default 0 → past EOF (whole-file trace). *)
  let end_at = if !end_at = 0 then line_count + 1 else !end_at + 1 in
  let on_cmd = Printf.sprintf "debug +%s;" !flags in
  let off_cmd = Printf.sprintf "debug -%s;" !flags in
  let probe, _mapping =
    Pp2lp.Lp_tools.make_probe ~original:!file
      ~insertions:[ (at, on_cmd); (end_at, off_cmd) ]
  in
  Fun.protect
    ~finally:(fun () -> Pp2lp.Lp_tools.cleanup_probe probe)
    (fun () ->
      let argv = [| "lambdapi"; "check"; probe |] in
      let rc, out, err = Pp2lp.Runner.run_capture argv in
      if !save_to <> "" then begin
        let oc = open_out !save_to in
        output_string oc (out ^ err);
        close_out oc
      end;
      if !raw then print_string (out ^ err)
      else begin
        (* Lambdapi puts command echoes on stdout and debug traces on
           stderr. The `debug +/-FLAGS;` toggles in the probe scope
           lambdapi's emission to that region — so stderr IS the
           bracketed trace. No further slicing required. *)
        let trace = String.trim err in
        let stat_lines =
          if trace = "" then 0
          else List.length (String.split_on_char '\n' trace)
        in
        Printf.eprintf "[lp-debug] flags=%s region=L%d-L%d rc=%d trace=%d lines%s\n"
          !flags at end_at rc stat_lines
          (if !save_to <> "" then " saved=" ^ !save_to else "");
        if trace = "" then begin
          if rc <> 0 then begin
            let formatted = Pp2lp.Lp_diag.format_for_terminal out in
            if String.trim formatted <> "" then print_string formatted
            else print_string out
          end else
            print_endline "(no debug events emitted in this region)"
        end else
          print_endline trace
      end;
      if rc <> 0 then exit rc)

(* ---- entry point ---- *)

let usage () =
  prerr_endline "Usage: pp2lp <command> [options]";
  prerr_endline "";
  prerr_endline "Emission / round-trip:";
  prerr_endline "  emit  REPLAY... [--json]    Emit Lambdapi .lp to stdout";
  prerr_endline "  parse REPLAY...             Parse replay (diagnostics only)";
  prerr_endline "  prove FORMULA               PP a formula and emit LP proof";
  prerr_endline "  synth GOALS DIR             Generate .but files from goals.txt";
  prerr_endline "";
  prerr_endline "Suite orchestration:";
  prerr_endline "  gen      [--suite=X] [--alloc=...] [--all]";
  prerr_endline "  check    [--suite=X] [--name=Y] [--fresh] [--all-failures]";
  prerr_endline "                              [--job=PFX] [--json]";
  prerr_endline "  status   [--suite=X]        Per-suite counts from cache (fast)";
  prerr_endline "  coverage [--by-suite] [--missing]";
  prerr_endline "  clean    [--lpo] [--cache] [--all] [--suite=X]";
  prerr_endline "";
  prerr_endline "Debugging:";
  prerr_endline "  debug REPLAY [--show=dispatch|tree|both]";
  prerr_endline "  show-fail SUITE NAME       Decode .cache/<NAME>.fail";
  prerr_endline "  diff REPLAY                Side-by-side PP vs LP listing";
  prerr_endline "";
  prerr_endline "Lambdapi tooling (file-level; no LSP):";
  prerr_endline "  lp-check FILE...   [--json] [--all-errors]";
  prerr_endline "  lp-axioms FILE...  [--scope=file|project] [--json]";
  prerr_endline "  lp-probe FILE LINE 'COMMAND;'   [--raw]";
  prerr_endline "                                  insert COMMAND at LINE in a";
  prerr_endline "                                  probe file, slice the relevant";
  prerr_endline "                                  output (compute/type/print/...)";
  prerr_endline "  lp-debug FILE --flags=FLAGS [--at=LINE] [--end-at=LINE]";
  prerr_endline "                              [--save-to=PATH] [--raw]";
  prerr_endline "                              scoped trace via debug +/-FLAGS;"

let () =
  if Array.length Sys.argv < 2 then begin usage (); exit 1 end;
  match Sys.argv.(1) with
  | "emit"      -> cmd_emit ()
  | "parse"     -> cmd_parse ()
  | "prove"     -> cmd_prove ()
  | "synth"     -> cmd_synth ()
  | "check"     -> cmd_check ()
  | "status"    -> cmd_status ()
  | "coverage"  -> cmd_coverage ()
  | "clean"     -> cmd_clean ()
  | "gen"       -> cmd_gen ()
  | "debug"     -> cmd_debug ()
  | "show-fail" -> cmd_show_fail ()
  | "diff"      -> cmd_diff ()
  | "lp-check"  -> cmd_lp_check ()
  | "lp-axioms" -> cmd_lp_axioms ()
  | "lp-debug"  -> cmd_lp_debug ()
  | "lp-probe"  -> cmd_lp_probe ()
  | "--help" | "-help" | "-h" -> usage ()
  | s ->
    Printf.eprintf "Unknown command: %s\n\n" s;
    usage ();
    exit 1
