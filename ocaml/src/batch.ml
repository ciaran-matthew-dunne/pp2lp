type config = {
  replay_dir: string;
  lp_dir: string;
  lp_pkg_dir: string;
  filter: string option;
  use_cache: bool;
  cache_file: string;
}

let discover_replays ~dir ~filter =
  let files = Sys.readdir dir in
  let files = Array.to_list files in
  let files = List.filter (fun f -> Filename.check_suffix f ".replay") files in
  let files = match filter with
    | None -> files
    | Some pat -> List.filter (fun f -> let len = String.length pat in
        String.length f >= len && String.sub f 0 len = pat) files
  in
  let files = List.sort String.compare files in
  List.map (fun f -> Filename.concat dir f) files

let run (cfg : config) : int =
  Check.ensure_dir cfg.lp_dir;
  let replays = discover_replays ~dir:cfg.replay_dir ~filter:cfg.filter in
  let total = List.length replays in
  if total = 0 then begin
    Printf.eprintf "No replay files found in %s" cfg.replay_dir;
    (match cfg.filter with
     | Some pat -> Printf.eprintf " matching '%s*'" pat
     | None -> ());
    Printf.eprintf "\n";
    1
  end else begin
    (* Load cache *)
    let cache_entries = if cfg.use_cache then Cache.load cfg.cache_file else [] in
    let ok = ref 0 in
    let fail = ref 0 in
    let skip = ref 0 in
    let emit_fail = ref 0 in
    let failures = Buffer.create 256 in
    let new_cache = ref cache_entries in
    List.iteri (fun i replay_path ->
      let idx = i + 1 in
      let name = Check.name_of_replay replay_path in
      (* Check cache *)
      if cfg.use_cache && Cache.is_cached cache_entries replay_path then begin
        incr skip;
        Printf.printf "[%3d/%d] SKIP  %s  (cached)\n%!" idx total name
      end else begin
        match Check.check_replay ~lp_dir:cfg.lp_dir ~lp_pkg_dir:cfg.lp_pkg_dir replay_path with
        | Check.Pass { elapsed; _ } ->
          incr ok;
          Printf.printf "[%3d/%d]  OK   %s  (%s)\n%!" idx total name (Check.format_time elapsed);
          (* Update cache *)
          let digest = Cache.digest_file replay_path in
          new_cache := { Cache.path = replay_path; digest } ::
            (List.filter (fun e -> e.Cache.path <> replay_path) !new_cache)
        | Check.Fail { lp_file; output; elapsed; _ } ->
          incr fail;
          Printf.printf "[%3d/%d] FAIL  %s  (%s)\n%!" idx total name (Check.format_time elapsed);
          (* Show error output indented *)
          let lines = String.split_on_char '\n' (String.trim output) in
          List.iter (fun line ->
            if String.length line > 0 then
              Printf.printf "         | %s\n" line
          ) lines;
          Buffer.add_string failures (Printf.sprintf "  %s\n" lp_file)
        | Check.Emit_error { msg; _ } ->
          incr emit_fail;
          Printf.printf "[%3d/%d] EMIT  %s\n%!" idx total name;
          Printf.printf "         | %s\n" msg
      end
    ) replays;
    (* Save cache *)
    if cfg.use_cache then Cache.save cfg.cache_file !new_cache;
    (* Summary *)
    Printf.printf "---\nResults: %d passed, %d failed, %d skipped" !ok !fail !skip;
    if !emit_fail > 0 then Printf.printf ", %d emit errors" !emit_fail;
    Printf.printf " (%d total)\n" total;
    if Buffer.length failures > 0 then begin
      Printf.printf "Failed:\n%s" (Buffer.contents failures)
    end;
    if !fail > 0 || !emit_fail > 0 then 1 else 0
  end
