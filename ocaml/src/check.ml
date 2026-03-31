type result =
  | Pass of { name: string; lp_file: string; elapsed: float }
  | Fail of { name: string; lp_file: string; output: string; elapsed: float }
  | Emit_error of { name: string; msg: string }

let name_of_replay (fp : string) : string =
  let base = Filename.basename fp in
  if Filename.check_suffix base ".trace.replay" then
    Filename.chop_suffix base ".trace.replay"
  else if Filename.check_suffix base ".replay" then
    Filename.chop_suffix base ".replay"
  else base

let format_time (t : float) : string =
  if t < 1.0 then Printf.sprintf "%.0fms" (t *. 1000.)
  else Printf.sprintf "%.1fs" t

let ensure_dir path =
  if not (Sys.file_exists path) then
    ignore (Sys.command (Printf.sprintf "mkdir -p %s" (Filename.quote path)))

let run_lambdapi ~lp_pkg_dir ~lp_file =
  let abs_lp =
    if Filename.is_relative lp_file then
      Filename.concat (Sys.getcwd ()) lp_file
    else lp_file
  in
  let cmd =
    Printf.sprintf "cd %s && lambdapi check %s 2>&1"
      (Filename.quote lp_pkg_dir) (Filename.quote abs_lp)
  in
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try
     while true do
       Buffer.add_string buf (input_line ic);
       Buffer.add_char buf '\n'
     done
   with End_of_file -> ());
  let status = Unix.close_process_in ic in
  (status, Buffer.contents buf)

let check_replay ~lp_dir ~lp_pkg_dir (replay_path : string) : result =
  let name = name_of_replay replay_path in
  let lp_file = Filename.concat lp_dir (name ^ ".lp") in
  match
    (try Ok (Reconstruct.reconstruct_file replay_path)
     with exn -> Error (Printexc.to_string exn))
  with
  | Error msg ->
    Emit_error { name; msg }
  | Ok lp_content ->
    let oc = open_out lp_file in
    output_string oc lp_content;
    close_out oc;
    let t0 = Unix.gettimeofday () in
    let status, output = run_lambdapi ~lp_pkg_dir ~lp_file in
    let elapsed = Unix.gettimeofday () -. t0 in
    (match status with
     | Unix.WEXITED 0 -> Pass { name; lp_file; elapsed }
     | _ -> Fail { name; lp_file; output; elapsed })
