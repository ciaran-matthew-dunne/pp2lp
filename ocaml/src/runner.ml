(* Per-test runner: emit + lambdapi check + cache writeback. *)

type outcome =
  | Pass of { trust : int; admit : int; cached : bool }
  | Skipped of { reason : string; cached : bool }
  | Failed of { detail : string; cached : bool }

(* Detected once per process: does `lambdapi check` accept --json? *)
let lambdapi_supports_json : bool option ref = ref None
let detect_lambdapi_json () =
  match !lambdapi_supports_json with
  | Some b -> b
  | None ->
    let cmd = "lambdapi check --help 2>&1 | grep -q -- '--json'" in
    let rc = Sys.command cmd in
    let b = (rc = 0) in
    lambdapi_supports_json := Some b;
    b

(* Read a whole file as a string. *)
let read_file path =
  let ic = open_in path in
  let s = In_channel.input_all ic in
  close_in ic;
  s

let write_file path s =
  let oc = open_out path in
  output_string oc s;
  close_out oc

(* Write the per-suite lambdapi.pkg if the contents would change. *)
let ensure_pkg suite =
  let pkg_path = Filename.concat (Suite.dir suite) "lambdapi.pkg" in
  let pkg_name = Suite.pkg_name suite in
  let want = Printf.sprintf "package_name = %s\nroot_path = %s\n"
               pkg_name pkg_name
  in
  let cur = try read_file pkg_path with _ -> "" in
  if cur <> want then write_file pkg_path want

(* Count occurrences of whole-word "trust" / "admit" in LP source.
   Mirrors the original `grep -ow`. We approximate by matching the
   keyword preceded and followed by a non-identifier character (or
   string boundary). *)
let count_word w s =
  let n = String.length s in
  let wl = String.length w in
  let is_word_char c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
    (c >= '0' && c <= '9') || c = '_'
  in
  let count = ref 0 in
  let i = ref 0 in
  while !i + wl <= n do
    if String.sub s !i wl = w
       && (!i = 0 || not (is_word_char s.[!i - 1]))
       && (!i + wl = n || not (is_word_char s.[!i + wl]))
    then begin
      incr count;
      i := !i + wl
    end else incr i
  done;
  !count

(* Run a command, capture combined stdout+stderr, return (status, text).
   Uses Unix.create_process so we can collect both streams. *)
let run_capture argv =
  let stdout_r, stdout_w = Unix.pipe () in
  let stderr_r, stderr_w = Unix.pipe () in
  let pid = Unix.create_process argv.(0) argv
              Unix.stdin stdout_w stderr_w
  in
  Unix.close stdout_w;
  Unix.close stderr_w;
  let read_all fd =
    let b = Buffer.create 4096 in
    let chunk = Bytes.create 4096 in
    let rec loop () =
      let n = Unix.read fd chunk 0 4096 in
      if n > 0 then begin
        Buffer.add_subbytes b chunk 0 n;
        loop ()
      end
    in
    loop ();
    Unix.close fd;
    Buffer.contents b
  in
  let out = read_all stdout_r in
  let err = read_all stderr_r in
  let _, status = Unix.waitpid [] pid in
  let rc = match status with
    | Unix.WEXITED n -> n
    | Unix.WSIGNALED n -> 128 + n
    | Unix.WSTOPPED n -> 128 + n
  in
  (rc, out, err)

(* Strip "Entering ..." / "Leaving ..." chatter from emit stderr.
   These are PP-trace fragments that leak through in some replays. *)
let filter_emit_warn s =
  String.split_on_char '\n' s
  |> List.filter (fun l ->
    let t = String.trim l in
    t <> "" &&
    not (let n = String.length t in
         (n >= 8 && String.sub t 0 8 = "Entering") ||
         (n >= 7 && String.sub t 0 7 = "Leaving")))
  |> String.concat "\n"

(* Run pp2lp's emit on one replay → returns (lp_text, exit_code, warn).
   Reuses the in-process emit pipeline so we don't fork. *)
let emit_in_process (replay : string) :
  [`Ok of string | `Skip of string | `Error of string] =
  Emit_lp.trace_file := replay;
  try
    let content = Reconstruct.reconstruct_symbol replay in
    let body = Emit_lp.lp_header ^ "\n" ^ content ^ "\n" in
    `Ok body
  with
  | Proof_tree.Ill_formed_replay msg -> `Skip msg
  | Proof_tree.Emit_admit msg -> `Error ("emit error: " ^ msg)
  | exn ->
    `Error (Printf.sprintf "ERROR: %s: %s" replay (Printexc.to_string exn))

(* Lambdapi-check the .lp file; returns (rc, output text). *)
let lambdapi_check (lp_path : string) =
  let json = detect_lambdapi_json () in
  let argv =
    if json then [| "lambdapi"; "check"; "--json"; "-c"; lp_path |]
    else [| "lambdapi"; "check"; "-c"; lp_path |]
  in
  let rc, out, err = run_capture argv in
  (rc, out ^ err)

type config = {
  suite : Suite.t;
  xfail : string list;
  sentinel : float;
}

(* Run one test. Updates cache markers. Returns the outcome.
   If [force] is true, ignores cache hits. *)
let run_one ~cfg ?(force=false) (name : string) : outcome =
  let suite_dir = Suite.dir cfg.suite in
  let replay = Filename.concat suite_dir (name ^ ".replay") in
  let outfile = Filename.concat suite_dir (name ^ ".lp") in
  let is_xfail = List.mem name cfg.xfail in
  let cache_hit =
    if force then None
    else Cache.lookup ~suite_dir ~name ~replay ~sentinel:cfg.sentinel
  in
  match cache_hit with
  | Some Cache.Ok ->
    let body =
      Cache.read_marker_body ~suite_dir ~name Cache.Ok
      |> Option.value ~default:""
    in
    let (t, a) = Cache.parse_ok_body body in
    Pass { trust = t; admit = a; cached = true }
  | Some Cache.Skip ->
    let body =
      Cache.read_marker_body ~suite_dir ~name Cache.Skip
      |> Option.value ~default:""
    in
    Skipped { reason = String.trim body; cached = true }
  | Some Cache.Fail ->
    let body =
      Cache.read_marker_body ~suite_dir ~name Cache.Fail
      |> Option.value ~default:""
    in
    Failed { detail = body; cached = true }
  | None ->
    Cache.clear_markers ~suite_dir ~name;
    match emit_in_process replay with
    | `Skip msg ->
      Cache.write_marker ~suite_dir ~name Cache.Skip msg;
      Skipped { reason = msg; cached = false }
    | `Error msg ->
      if is_xfail then begin
        let r = "xfail (emit error: " ^ msg ^ ")" in
        Cache.write_marker ~suite_dir ~name Cache.Skip r;
        Skipped { reason = r; cached = false }
      end else begin
        Cache.write_marker ~suite_dir ~name Cache.Fail msg;
        Failed { detail = msg; cached = false }
      end
    | `Ok lp_text ->
      write_file outfile lp_text;
      (* Empty / no-symbol emission is treated as failure. *)
      let has_symbol =
        let rec scan i =
          if i + 6 > String.length lp_text then false
          else if String.sub lp_text i 6 = "symbol" then true
          else scan (i + 1)
        in
        scan 0
      in
      if not has_symbol then begin
        let msg = "empty emission" in
        if is_xfail then begin
          Cache.write_marker ~suite_dir ~name Cache.Skip
            "xfail (empty emission)";
          Skipped { reason = "xfail (empty emission)"; cached = false }
        end else begin
          Cache.write_marker ~suite_dir ~name Cache.Fail msg;
          Failed { detail = msg; cached = false }
        end
      end else begin
        let rc, output = lambdapi_check outfile in
        if rc = 0 then begin
          let trust = count_word "trust" lp_text in
          let admit = count_word "admit" lp_text in
          let body = Printf.sprintf "%d %d" trust admit in
          Cache.write_marker ~suite_dir ~name Cache.Ok body;
          Pass { trust; admit; cached = false }
        end else begin
          if is_xfail then begin
            Cache.write_marker ~suite_dir ~name Cache.Skip
              "xfail (lambdapi error)";
            Skipped { reason = "xfail (lambdapi error)"; cached = false }
          end else begin
            Cache.write_marker ~suite_dir ~name Cache.Fail output;
            Failed { detail = output; cached = false }
          end
        end
      end

(* Discover all replay test names in a suite, sorted. *)
let list_tests suite =
  let dir = Suite.dir suite in
  if not (Cache.exists dir) then []
  else begin
    let dh = Unix.opendir dir in
    let acc = ref [] in
    (try while true do
      let name = Unix.readdir dh in
      if Filename.check_suffix name ".replay"
      then acc := Filename.chop_suffix name ".replay" :: !acc
    done with End_of_file -> ());
    Unix.closedir dh;
    List.sort compare !acc
  end
