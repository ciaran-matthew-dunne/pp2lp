(* pp2lp CLI entry point. Subcommands are dispatched on Sys.argv.(1).
   Each command parses its own arg vector with Arg.parse_argv. *)

let die fmt = Printf.ksprintf (fun s ->
  prerr_string s; prerr_newline (); exit 1) fmt

let getenv_opt s = try Some (Sys.getenv s) with Not_found -> None

let pp2lp_binary () = Sys.executable_name

let lp_dir () =
  match getenv_opt "PP2LP_ROOT" with
  | Some r -> Filename.concat r "lp"
  | None -> "lp"

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

let make_cache_cfg suite ~xfail =
  let sentinel =
    Pp2lp.Cache.compute_sentinel
      ~bin_path:(pp2lp_binary ())
      ~lp_dir:(lp_dir ())
  in
  { Pp2lp.Runner.suite; xfail; sentinel }

let parse_suite_arg s =
  if not (Pp2lp.Suite.exists s) then
    die "Unknown suite %S (known: %s)" s
      (String.concat ", " (Pp2lp.Suite.names ()));
  Pp2lp.Suite.find s

(* ---- emit ---- *)

let cmd_emit () =
  let files = ref [] in
  let argv = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Arg.parse_argv argv
    [ "-debug",     Arg.Set Pp2lp.Proof_tree.debug,
        " Show proof tree debug output";
      "-debug-ins", Arg.Set Pp2lp.Ins.debug_ctx,
        " Dump hyp context on INS failure";
      "-trace",     Arg.Set Pp2lp.Emit_lp.trace,
        " Log emit-dispatch decisions to stderr (one line per case)" ]
    (fun f -> files := f :: !files)
    "Usage: pp2lp emit [-debug] [-debug-ins] [-trace] file1.replay ...";
  let files = List.rev !files in
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
  match List.rev !warn_parts with
  | [] -> main
  | xs -> Printf.sprintf "%s [%s]" main (String.concat ", " xs)

let cmd_check () =
  let suite_name = ref "prv" in
  let job = ref "" in
  let name = ref "" in
  let fresh = ref false in
  let all_failures = ref false in
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
        " Report all failures instead of fast-fail" ]
    (fun s ->
      die "check: unexpected positional arg %S (use --name=%s)" s s)
    "Usage: pp2lp check [--suite=X] [--name=Y] [--job=PFX] [--fresh] \
                       [--all-failures]";
  let suite = parse_suite_arg !suite_name in
  let suite_dir = Pp2lp.Suite.dir suite in
  if !fresh then begin
    Pp2lp.Cache.clear_all suite_dir;
    drop_lpo_files ()
  end;
  let cfg = make_cache_cfg suite ~xfail:[] in
  Pp2lp.Runner.ensure_lp_dir suite;
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
  in
  let summarise () =
    if !name <> "" then ()
    else begin
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
  if !all then List.iter run_one Pp2lp.Suite.all
  else run_one (parse_suite_arg !suite_name)

(* ---- entry point ---- *)

let usage () =
  prerr_endline "Usage: pp2lp <command> [options]";
  prerr_endline "";
  prerr_endline "Emission / round-trip:";
  prerr_endline "  emit  REPLAY...             Emit Lambdapi .lp to stdout";
  prerr_endline "  prove FORMULA               PP a formula and emit LP proof";
  prerr_endline "";
  prerr_endline "Suite orchestration:";
  prerr_endline "  gen      [--suite=X] [--alloc=...] [--all]";
  prerr_endline "  check    [--suite=X] [--name=Y] [--fresh] [--all-failures] [--job=PFX]";
  prerr_endline "  status   [--suite=X]";
  prerr_endline "  clean    [--lpo] [--cache] [--all] [--suite=X]"

let () =
  if Array.length Sys.argv < 2 then begin usage (); exit 1 end;
  match Sys.argv.(1) with
  | "emit"      -> cmd_emit ()
  | "prove"     -> cmd_prove ()
  | "synth"     -> cmd_synth ()
  | "check"     -> cmd_check ()
  | "status"    -> cmd_status ()
  | "clean"     -> cmd_clean ()
  | "gen"       -> cmd_gen ()
  | "--help" | "-help" | "-h" -> usage ()
  | s ->
    Printf.eprintf "Unknown command: %s\n\n" s;
    usage ();
    exit 1
