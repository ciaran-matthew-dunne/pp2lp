(* Per-test cache: bench/<suite>/.cache/<name>.{ok,fail,skip}.

   Marker semantics, preserved from the original Makefile:
     • <name>.ok    — passed last time. Body may be "<trust> <admit>"
                      (whitespace-separated ints) for status reporting.
     • <name>.fail  — failed last time. Body is the lambdapi error blob.
     • <name>.skip  — emit raised Ill_formed_replay (upstream gen
                      failure surfaced late, e.g. truncated replay).
                      Body is a free-form reason (single line). These
                      count as gen-fail in `pp2lp status`.

   A marker is "fresh" iff its mtime is ≥ the sentinel mtime, where the
   sentinel is max(pp2lp binary mtime, newest lp/**/*.lp mtime).
   Additionally the marker must be newer than the .replay it covers. *)

type kind = Ok | Fail | Skip

let kind_ext = function Ok -> ".ok" | Fail -> ".fail" | Skip -> ".skip"

let kind_of_ext s =
  if Filename.check_suffix s ".ok" then Some Ok
  else if Filename.check_suffix s ".fail" then Some Fail
  else if Filename.check_suffix s ".skip" then Some Skip
  else None

let mtime path =
  try (Unix.stat path).Unix.st_mtime
  with Unix.Unix_error _ -> 0.0

let exists path =
  try ignore (Unix.stat path); true
  with Unix.Unix_error _ -> false

let marker_path ~suite_dir ~name kind =
  Filename.concat (Filename.concat suite_dir ".cache") (name ^ kind_ext kind)

let cache_dir suite_dir = Filename.concat suite_dir ".cache"

let ensure_cache_dir suite_dir =
  let d = cache_dir suite_dir in
  (try Unix.mkdir (Filename.dirname d) 0o755
   with Unix.Unix_error _ -> ());
  (try Unix.mkdir d 0o755
   with Unix.Unix_error _ -> ())

(* Walk lp/ for *.lp files, collecting newest mtime. *)
let rec walk_dir_for_lp acc dir =
  let acc = ref acc in
  (try
    let dh = Unix.opendir dir in
    (try
      while true do
        let name = Unix.readdir dh in
        if name <> "." && name <> ".." then begin
          let p = Filename.concat dir name in
          let st = try Some (Unix.stat p) with Unix.Unix_error _ -> None in
          match st with
          | Some { Unix.st_kind = Unix.S_DIR; _ } ->
            acc := walk_dir_for_lp !acc p
          | Some { Unix.st_kind = Unix.S_REG; st_mtime; _ }
            when Filename.check_suffix name ".lp" ->
            if st_mtime > !acc then acc := st_mtime
          | _ -> ()
        end
      done
    with End_of_file -> ());
    Unix.closedir dh
  with Unix.Unix_error _ -> ());
  !acc

(* Compute the sentinel: max(pp2lp binary mtime, max lp/ mtime).
   [bin_path] is the executable path used for resolution. If absent,
   contributes 0. *)
let compute_sentinel ~bin_path ~lp_dir : float =
  let bin_mt = mtime bin_path in
  let lp_mt = walk_dir_for_lp 0.0 lp_dir in
  max bin_mt lp_mt

(* Decide whether the existing markers for a single test count as
   "fresh enough to skip running again". Returns the kind that was
   fresh, or None. Fresh means: marker exists, marker is newer than
   the replay, and marker mtime ≥ sentinel.

   Order matters: a fresh .ok wins over a fresh .skip wins over a
   fresh .fail. The original Makefile checked .ok first, .skip
   second, .fail third — same precedence here. *)
let lookup ~suite_dir ~name ~replay ~sentinel : kind option =
  let replay_mt = mtime replay in
  let check kind =
    let m = marker_path ~suite_dir ~name kind in
    if exists m then begin
      let mm = mtime m in
      if mm > replay_mt && mm >= sentinel then Some kind
      else None
    end else None
  in
  match check Ok with
  | Some _ as r -> r
  | None ->
    match check Skip with
    | Some _ as r -> r
    | None -> check Fail

let read_marker_body ~suite_dir ~name kind =
  let p = marker_path ~suite_dir ~name kind in
  try
    let ic = open_in p in
    let s = In_channel.input_all ic in
    close_in ic;
    Some s
  with _ -> None

(* Parse "<trust> <admit>" from an .ok body. Empty/missing → (0, 0). *)
let parse_ok_body body =
  let body = String.trim body in
  if body = "" then (0, 0)
  else
    let parts = String.split_on_char ' ' body in
    let parts = List.filter (fun s -> s <> "") parts in
    match parts with
    | [t; a] ->
      (try (int_of_string t, int_of_string a) with _ -> (0, 0))
    | [t] -> (try (int_of_string t, 0) with _ -> (0, 0))
    | _ -> (0, 0)

let write_marker ~suite_dir ~name kind body =
  ensure_cache_dir suite_dir;
  let p = marker_path ~suite_dir ~name kind in
  let oc = open_out p in
  output_string oc body;
  close_out oc

let clear_markers ~suite_dir ~name =
  List.iter (fun k ->
    let p = marker_path ~suite_dir ~name k in
    try Unix.unlink p with Unix.Unix_error _ -> ()
  ) [Ok; Fail; Skip]

(* List all (name, kind) pairs in a suite's cache. Best effort — silent
   on missing dirs. *)
let list_markers suite_dir =
  let d = cache_dir suite_dir in
  if not (exists d) then []
  else begin
    let dh = Unix.opendir d in
    let acc = ref [] in
    (try
      while true do
        let name = Unix.readdir dh in
        match kind_of_ext name with
        | Some k ->
          let stem = Filename.chop_extension name in
          acc := (stem, k) :: !acc
        | None -> ()
      done
    with End_of_file -> ());
    Unix.closedir dh;
    !acc
  end

(* Remove the .cache directory entirely. *)
let clear_all suite_dir =
  let d = cache_dir suite_dir in
  if exists d then begin
    let dh = Unix.opendir d in
    let names = ref [] in
    (try
      while true do
        let name = Unix.readdir dh in
        if name <> "." && name <> ".."
        then names := name :: !names
      done
    with End_of_file -> ());
    Unix.closedir dh;
    List.iter (fun n ->
      try Unix.unlink (Filename.concat d n)
      with Unix.Unix_error _ -> ()
    ) !names;
    try Unix.rmdir d with Unix.Unix_error _ -> ()
  end
