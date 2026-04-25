(* Cache-logic regression tests.
   The cache logic is the gnarly bit of the migration — pull the
   mtime/sentinel rules into typed code and pin them in tests so a
   refactor can't silently weaken the freshness check. *)

open Pp2lp

(* --- helpers --- *)

let failures = ref 0
let total = ref 0

let check label cond =
  incr total;
  if not cond then begin
    incr failures;
    Printf.printf "  FAIL: %s\n" label
  end

(* mktemp-style: returns a unique scratch dir under /tmp/pp2lp-test-XXX. *)
let scratch_dir () =
  let base = Filename.temp_file "pp2lp-test-" "" in
  Sys.remove base;
  Unix.mkdir base 0o755;
  base

let touch ?(mtime=Unix.gettimeofday ()) path =
  let oc = open_out path in
  close_out oc;
  Unix.utimes path mtime mtime

let set_mtime path t = Unix.utimes path t t

(* Recursively remove a directory tree. *)
let rec rmrf path =
  match (try Some (Unix.lstat path) with _ -> None) with
  | None -> ()
  | Some { st_kind = Unix.S_DIR; _ } ->
    let dh = Unix.opendir path in
    let entries = ref [] in
    (try while true do
      let n = Unix.readdir dh in
      if n <> "." && n <> ".." then entries := n :: !entries
    done with End_of_file -> ());
    Unix.closedir dh;
    List.iter (fun n -> rmrf (Filename.concat path n)) !entries;
    (try Unix.rmdir path with _ -> ())
  | _ -> (try Unix.unlink path with _ -> ())

(* --- tests --- *)

let test_marker_paths () =
  let suite_dir = "/tmp/foo" in
  check "ok marker path"
    (Cache.marker_path ~suite_dir ~name:"x" Cache.Ok = "/tmp/foo/.cache/x.ok");
  check "fail marker path"
    (Cache.marker_path ~suite_dir ~name:"x" Cache.Fail = "/tmp/foo/.cache/x.fail");
  check "skip marker path"
    (Cache.marker_path ~suite_dir ~name:"x" Cache.Skip = "/tmp/foo/.cache/x.skip")

let test_kind_of_ext () =
  check "ext .ok"  (Cache.kind_of_ext "x.ok" = Some Cache.Ok);
  check "ext .fail" (Cache.kind_of_ext "x.fail" = Some Cache.Fail);
  check "ext .skip" (Cache.kind_of_ext "x.skip" = Some Cache.Skip);
  check "ext other" (Cache.kind_of_ext "x.lp" = None)

let test_parse_ok_body () =
  check "empty body" (Cache.parse_ok_body "" = (0, 0));
  check "two ints" (Cache.parse_ok_body "3 5" = (3, 5));
  check "one int" (Cache.parse_ok_body "7" = (7, 0));
  check "with newline" (Cache.parse_ok_body "  9 0\n" = (9, 0));
  check "garbage" (Cache.parse_ok_body "garbage" = (0, 0))

(* Core lookup: marker fresh iff mtime > replay AND mtime ≥ sentinel. *)
let test_lookup_fresh_ok () =
  let dir = scratch_dir () in
  let cleanup () = rmrf dir in
  Fun.protect ~finally:cleanup (fun () ->
    let replay = Filename.concat dir "x.replay" in
    let now = Unix.gettimeofday () in
    touch ~mtime:(now -. 100.0) replay;
    Cache.write_marker ~suite_dir:dir ~name:"x" Cache.Ok "0 0";
    let m = Cache.marker_path ~suite_dir:dir ~name:"x" Cache.Ok in
    set_mtime m (now -. 50.0);
    (* Sentinel is older than the marker → fresh. *)
    let r = Cache.lookup ~suite_dir:dir ~name:"x" ~replay
              ~sentinel:(now -. 75.0) in
    check "fresh .ok wins" (r = Some Cache.Ok))

let test_lookup_marker_older_than_replay () =
  let dir = scratch_dir () in
  Fun.protect ~finally:(fun () -> rmrf dir) (fun () ->
    let replay = Filename.concat dir "x.replay" in
    let now = Unix.gettimeofday () in
    touch ~mtime:(now -. 10.0) replay;
    Cache.write_marker ~suite_dir:dir ~name:"x" Cache.Ok "";
    let m = Cache.marker_path ~suite_dir:dir ~name:"x" Cache.Ok in
    set_mtime m (now -. 50.0);
    (* Marker older than replay → stale. *)
    let r = Cache.lookup ~suite_dir:dir ~name:"x" ~replay
              ~sentinel:(now -. 100.0) in
    check "stale: marker older than replay" (r = None))

let test_lookup_marker_older_than_sentinel () =
  let dir = scratch_dir () in
  Fun.protect ~finally:(fun () -> rmrf dir) (fun () ->
    let replay = Filename.concat dir "x.replay" in
    let now = Unix.gettimeofday () in
    touch ~mtime:(now -. 100.0) replay;
    Cache.write_marker ~suite_dir:dir ~name:"x" Cache.Ok "";
    let m = Cache.marker_path ~suite_dir:dir ~name:"x" Cache.Ok in
    set_mtime m (now -. 50.0);
    (* Sentinel newer than marker → stale. *)
    let r = Cache.lookup ~suite_dir:dir ~name:"x" ~replay
              ~sentinel:(now -. 10.0) in
    check "stale: marker older than sentinel" (r = None))

(* Precedence: .ok > .skip > .fail when all three are fresh. *)
let test_lookup_precedence () =
  let dir = scratch_dir () in
  Fun.protect ~finally:(fun () -> rmrf dir) (fun () ->
    let replay = Filename.concat dir "x.replay" in
    let now = Unix.gettimeofday () in
    touch ~mtime:(now -. 200.0) replay;
    Cache.write_marker ~suite_dir:dir ~name:"x" Cache.Ok "";
    Cache.write_marker ~suite_dir:dir ~name:"x" Cache.Skip "";
    Cache.write_marker ~suite_dir:dir ~name:"x" Cache.Fail "";
    let r = Cache.lookup ~suite_dir:dir ~name:"x" ~replay
              ~sentinel:(now -. 100.0) in
    check ".ok wins over .skip and .fail" (r = Some Cache.Ok);
    Unix.unlink (Cache.marker_path ~suite_dir:dir ~name:"x" Cache.Ok);
    let r = Cache.lookup ~suite_dir:dir ~name:"x" ~replay
              ~sentinel:(now -. 100.0) in
    check ".skip wins over .fail" (r = Some Cache.Skip))

(* clear_markers leaves nothing behind. *)
let test_clear_markers () =
  let dir = scratch_dir () in
  Fun.protect ~finally:(fun () -> rmrf dir) (fun () ->
    Cache.write_marker ~suite_dir:dir ~name:"x" Cache.Ok "";
    Cache.write_marker ~suite_dir:dir ~name:"x" Cache.Skip "";
    Cache.clear_markers ~suite_dir:dir ~name:"x";
    let exists kind =
      Cache.exists (Cache.marker_path ~suite_dir:dir ~name:"x" kind) in
    check "ok cleared"   (not (exists Cache.Ok));
    check "skip cleared" (not (exists Cache.Skip));
    check "fail cleared" (not (exists Cache.Fail)))

(* clear_all removes the .cache dir entirely. *)
let test_clear_all () =
  let dir = scratch_dir () in
  Fun.protect ~finally:(fun () -> rmrf dir) (fun () ->
    Cache.write_marker ~suite_dir:dir ~name:"x" Cache.Ok "";
    Cache.write_marker ~suite_dir:dir ~name:"y" Cache.Fail "boom";
    Cache.clear_all dir;
    check "cache dir gone"
      (not (Cache.exists (Filename.concat dir ".cache"))))

(* compute_sentinel: max of binary and lp dir. *)
let test_compute_sentinel () =
  let dir = scratch_dir () in
  Fun.protect ~finally:(fun () -> rmrf dir) (fun () ->
    let bin = Filename.concat dir "fakebin" in
    let lp_dir = Filename.concat dir "lp" in
    Unix.mkdir lp_dir 0o755;
    let lp_a = Filename.concat lp_dir "a.lp" in
    let lp_b = Filename.concat lp_dir "b.lp" in
    let now = Unix.gettimeofday () in
    touch ~mtime:(now -. 300.0) bin;
    touch ~mtime:(now -. 200.0) lp_a;
    touch ~mtime:(now -. 100.0) lp_b;
    let s = Cache.compute_sentinel ~bin_path:bin ~lp_dir in
    (* Newest is lp_b at now-100. *)
    check "sentinel = newest"
      (abs_float (s -. (now -. 100.0)) < 2.0);
    (* Update bin to be newest. *)
    let bin_t = now -. 50.0 in
    set_mtime bin bin_t;
    let s2 = Cache.compute_sentinel ~bin_path:bin ~lp_dir in
    check "sentinel = newer bin"
      (abs_float (s2 -. bin_t) < 2.0))

(* compute_sentinel walks subdirectories. *)
let test_compute_sentinel_recursive () =
  let dir = scratch_dir () in
  Fun.protect ~finally:(fun () -> rmrf dir) (fun () ->
    let lp_dir = Filename.concat dir "lp" in
    let lp_sub = Filename.concat lp_dir "rules" in
    Unix.mkdir lp_dir 0o755;
    Unix.mkdir lp_sub 0o755;
    let outer = Filename.concat lp_dir "a.lp" in
    let inner = Filename.concat lp_sub "b.lp" in
    let now = Unix.gettimeofday () in
    touch ~mtime:(now -. 200.0) outer;
    touch ~mtime:(now -. 50.0) inner;
    let s = Cache.compute_sentinel ~bin_path:"/no/such/file" ~lp_dir in
    check "recursive sentinel sees subdir lp"
      (abs_float (s -. (now -. 50.0)) < 2.0))

(* list_markers returns (stem, kind) pairs. *)
let test_list_markers () =
  let dir = scratch_dir () in
  Fun.protect ~finally:(fun () -> rmrf dir) (fun () ->
    Cache.write_marker ~suite_dir:dir ~name:"a" Cache.Ok "";
    Cache.write_marker ~suite_dir:dir ~name:"b" Cache.Fail "";
    Cache.write_marker ~suite_dir:dir ~name:"c" Cache.Skip "";
    let m = Cache.list_markers dir in
    let m = List.sort compare m in
    check "list_markers count" (List.length m = 3);
    check "list_markers entries"
      (m = [("a", Cache.Ok); ("b", Cache.Fail); ("c", Cache.Skip)]))

(* End-to-end: status reads list_markers properly. *)
let test_marker_body_roundtrip () =
  let dir = scratch_dir () in
  Fun.protect ~finally:(fun () -> rmrf dir) (fun () ->
    Cache.write_marker ~suite_dir:dir ~name:"a" Cache.Ok "12 3";
    let body = Cache.read_marker_body ~suite_dir:dir ~name:"a" Cache.Ok in
    check "roundtrip body" (body = Some "12 3");
    let (t, a) = Cache.parse_ok_body (Option.get body) in
    check "parsed counts" (t = 12 && a = 3))

let () =
  test_marker_paths ();
  test_kind_of_ext ();
  test_parse_ok_body ();
  test_lookup_fresh_ok ();
  test_lookup_marker_older_than_replay ();
  test_lookup_marker_older_than_sentinel ();
  test_lookup_precedence ();
  test_clear_markers ();
  test_clear_all ();
  test_compute_sentinel ();
  test_compute_sentinel_recursive ();
  test_list_markers ();
  test_marker_body_roundtrip ();
  Printf.printf "%d/%d cache tests passed\n"
    (!total - !failures) !total;
  if !failures > 0 then exit 1
