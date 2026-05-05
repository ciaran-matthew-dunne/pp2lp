(* Suite metadata — single source of truth for per-suite knobs. *)

type t = {
  name : string;
  (* Suite synthesises .but files from goals.txt before generating
     replays. Currently: claude, claude-arith. *)
  synth : bool;
  (* Default `krt -a` allocator string passed to gen_traces.py. Empty
     string means "use krt's defaults". *)
  alloc : string;
}

let all : t list = [
  { name = "claude";       synth = true;  alloc = "" };
  { name = "claude-arith"; synth = true;  alloc = "" };
  { name = "prv";          synth = false; alloc = "g50000" };
  { name = "og";           synth = false; alloc = "" };
]

let find name =
  match List.find_opt (fun s -> s.name = name) all with
  | Some s -> s
  | None -> failwith (Printf.sprintf "unknown suite %S" name)

let exists name = List.exists (fun s -> s.name = name) all

let names () = List.map (fun s -> s.name) all

(* Replay/trace inputs, cache markers, and synth artefacts live here. *)
let dir suite = Filename.concat "bench" suite.name
let cache_dir suite = Filename.concat (dir suite) ".cache"

(* Emitted .lp output lives under the pp2lp package so it doesn't
   need a separate lambdapi.pkg or a lib_root symlink. *)
let lp_dir suite =
  Filename.concat (Filename.concat "lp" "bench") suite.name
