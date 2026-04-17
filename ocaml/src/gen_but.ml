open Syntax_pp

(* ---- Split implication ---- *)

(* Split a formula at the outermost implication: H1 ∧ H2 ∧ ... ⇒ G
   Returns (hypotheses, goal). If no implication, returns ([], formula). *)
let split_imp prd =
  match prd with
  | Binary (Imp, lhs, goal) -> (Pp_lp.conj_leaves lhs, goal)
  | _ -> ([], prd)

(* ---- .but file generation ---- *)

let gen_but_content ?(name="pp2lp_query") (hyps : prd list) (goal : prd) : string =
  let buf = Buffer.create 512 in
  Printf.bprintf buf
    "Flag(TypeOn(\"%s\")) \
     & Flag(FileOn(\"%s.res\")) \
     & Set(Valid.1 | Rule(Implication | " name name;
  (* Hypotheses *)
  begin match hyps with
  | [] ->
    (* PP requires a non-empty hypothesis field; use ⊤ as a no-op *)
    Buffer.add_string buf "VRAI"
  | _ ->
    List.iteri (fun i h ->
      if i > 0 then Buffer.add_string buf " & ";
      Emit_pp.prd_to_pp_buf buf h
    ) hyps
  end;
  (* Goal and closing *)
  Buffer.add_string buf " | ? | ? | ";
  Emit_pp.prd_to_pp_buf buf goal;
  Buffer.add_string buf " | nn))";
  Buffer.contents buf

(* Generate a .but file from a single formula (hyps ⇒ goal) *)
let gen_but ?(name="pp2lp_query") (formula : prd) : string =
  let (hyps, goal) = split_imp formula in
  gen_but_content ~name hyps goal

(* ---- Full pipeline: formula → LP proof ---- *)

let find_krt () =
  let paths = [
    "/opt/atelierb-free-24.04.2/bin/krt";
    "/usr/local/bin/krt";
  ] in
  match List.find_opt Sys.file_exists paths with
  | Some p -> p
  | None ->
    (* Try PATH *)
    let ic = Unix.open_process_in "which krt 2>/dev/null" in
    let result = try Some (input_line ic) with End_of_file -> None in
    ignore (Unix.close_process_in ic);
    match result with
    | Some p -> String.trim p
    | None -> failwith "krt not found"

let find_kin name =
  let paths = [
    Printf.sprintf "/opt/atelierb-free-24.04.2/bin/%s" name;
    Printf.sprintf "%s/atelierb/bin/%s" (Sys.getenv "HOME") name;
  ] in
  match List.find_opt Sys.file_exists paths with
  | Some p -> p
  | None -> failwith (Printf.sprintf "%s not found" name)

(* Run a command, return (exit_code, stdout).
   stderr goes to /dev/null to avoid polluting captured output. *)
let run_cmd args cwd =
  let cmd = String.concat " " (List.map Filename.quote args) in
  let full = Printf.sprintf "cd %s && %s 2>/dev/null" (Filename.quote cwd) cmd in
  let ic = Unix.open_process_in full in
  let buf = Buffer.create 256 in
  (try while true do
    Buffer.add_string buf (input_line ic);
    Buffer.add_char buf '\n'
  done with End_of_file -> ());
  let status = Unix.close_process_in ic in
  let code = match status with Unix.WEXITED c -> c | _ -> 1 in
  (code, Buffer.contents buf)

(* prove: formula → LP proof string *)
let prove ?(name="pp2lp_query") (formula : prd) : string =
  let but_content = gen_but ~name formula in
  let krt = find_krt () in
  let pp_kin = find_kin "PP.kin" in
  let replay_kin = find_kin "REPLAY.kin" in
  (* Create temp directory *)
  let tmpdir = Filename.temp_dir "pp2lp" "" in
  let but_file = Filename.concat tmpdir (name ^ ".but") in
  let goal_file = Filename.concat tmpdir (name ^ ".goal") in
  let trace_file = name ^ ".trace" in
  let res_file = name ^ ".res" in
  let replay_goal_file = Filename.concat tmpdir (name ^ ".replay.goal") in
  let replay_res_file = name ^ ".replay.res" in
  let replay_file = Filename.concat tmpdir (name ^ ".trace.replay") in
  (* Write .but *)
  let oc = open_out but_file in
  output_string oc but_content;
  close_out oc;
  (* Convert .but → .goal (add TraceOn flag) *)
  let goal_content =
    Printf.sprintf "Flag(TraceOn(\"%s\")) & Flag(FileOn(\"%s\")) & %s"
      trace_file res_file
      (let s = but_content in
       (* Remove the TypeOn and FileOn flags, keep Set(...) *)
       match String.split_on_char '&' s with
       | _ :: _ :: rest -> String.concat "&" rest |> String.trim
       | _ -> s)
  in
  let oc = open_out goal_file in
  output_string oc goal_content;
  close_out oc;
  (* Run PP *)
  let (pp_code, pp_out) =
    run_cmd [krt; "-b"; pp_kin; Filename.basename goal_file] tmpdir in
  if pp_code <> 0 then
    failwith (Printf.sprintf "PP failed (exit %d): %s" pp_code pp_out);
  (* Check trace file exists *)
  let trace_path = Filename.concat tmpdir trace_file in
  if not (Sys.file_exists trace_path) then
    failwith (Printf.sprintf "PP did not produce trace file: %s" trace_path);
  (* Create replay goal *)
  let replay_content =
    Printf.sprintf "Flag(FileOn(\"%s\")) & (\"%s\")" replay_res_file trace_file
  in
  let oc = open_out replay_goal_file in
  output_string oc replay_content;
  close_out oc;
  (* Run REPLAY — captures stdout which contains the replay *)
  let (replay_code, replay_out) =
    run_cmd [krt; "-b"; replay_kin; Filename.basename replay_goal_file] tmpdir in
  if replay_code <> 0 then
    failwith (Printf.sprintf "REPLAY failed (exit %d): %s" replay_code replay_out);
  if String.length replay_out <= 10 then
    failwith "REPLAY produced no output";
  (* Write replay stdout to file *)
  let oc = open_out replay_file in
  output_string oc replay_out;
  close_out oc;
  (* Parse replay and emit LP *)
  let result = Reconstruct.reconstruct_file replay_file in
  (* Cleanup *)
  (try
    Array.iter (fun f ->
      Sys.remove (Filename.concat tmpdir f)
    ) (Sys.readdir tmpdir);
    Unix.rmdir tmpdir
  with _ -> ());
  result
