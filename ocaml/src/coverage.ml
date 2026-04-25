(* Per-rule coverage matrix across benchmark suites. Replaces
   bench/rule_coverage.sh. *)

(* All rules known to the rule_db, sorted alphabetically. *)
let all_rules () =
  let acc = Hashtbl.fold (fun k _ a -> k :: a) Rule_db.rules [] in
  (* Filter phantom entries (arity -1): they don't show up in replays. *)
  let acc = List.filter (fun n ->
    match Hashtbl.find_opt Rule_db.rules n with
    | Some r -> r.arity >= 0
    | None -> true) acc
  in
  List.sort compare acc

(* Extract the rule names that appear in a replay file.
   Rules look like "[NAME]" or "[NAME(ARG)]" at line start. _1 suffix
   stripped to fold primed variants together. *)
let rules_in_file path =
  let acc = ref [] in
  (try
    let ic = open_in path in
    (try while true do
      let line = input_line ic in
      let line = String.trim line in
      if String.length line > 1 && line.[0] = '[' then begin
        match String.index_opt line ']' with
        | Some j ->
          let inner = String.sub line 1 (j - 1) in
          (* Strip "(arg)" from inside *)
          let base = match String.index_opt inner '(' with
            | Some k -> String.sub inner 0 k
            | None -> inner
          in
          (* Strip trailing _1 *)
          let base =
            let n = String.length base in
            if n > 2 && String.sub base (n - 2) 2 = "_1"
            then String.sub base 0 (n - 2)
            else base
          in
          if String.length base > 0 &&
             let c = base.[0] in c >= 'A' && c <= 'Z'
          then acc := base :: !acc
        | None -> ()
      end
    done with End_of_file -> ());
    close_in ic
  with Sys_error _ -> ());
  !acc

let replays_in suite =
  let dir = Suite.dir suite in
  if not (Cache.exists dir) then []
  else
    let dh = Unix.opendir dir in
    let acc = ref [] in
    (try while true do
      let name = Unix.readdir dh in
      if Filename.check_suffix name ".replay"
      then acc := Filename.concat dir name :: !acc
    done with End_of_file -> ());
    Unix.closedir dh;
    !acc

(* Collect rule sets per suite. Returns (suite_name, rule_set) list,
   only for suites that have replays. *)
let by_suite () =
  Suite.all
  |> List.filter_map (fun s ->
    let files = replays_in s in
    if files = [] then None
    else begin
      let module SS = Set.Make(String) in
      let r =
        List.fold_left (fun acc f ->
          List.fold_left (fun acc r -> SS.add r acc) acc (rules_in_file f))
          SS.empty files
      in
      Some (s.Suite.name, r)
    end)

(* Render the per-suite × per-rule matrix to stdout. *)
let print_by_suite ?(missing=false) () =
  let module SS = Set.Make(String) in
  let suites = by_suite () in
  let rules = all_rules () in
  let header_abbrev = function
    | "claude" -> "CLA"
    | "claude-arith" -> "ARI"
    | "prv" -> "PRV"
    | "og" -> "OG "
    | "fuzz" -> "FUZ"
    | s -> if String.length s >= 3 then String.sub s 0 3 else s
  in
  Printf.printf "%-14s" "RULE";
  List.iter (fun (n, _) -> Printf.printf " %4s" (header_abbrev n)) suites;
  print_newline ();
  Printf.printf "%-14s" "----";
  List.iter (fun _ -> Printf.printf " %4s" "----") suites;
  print_newline ();
  List.iter (fun rule ->
    let any_hit = ref false in
    let cells = List.map (fun (_, set) ->
      if SS.mem rule set then begin any_hit := true; "*" end
      else "-"
    ) suites in
    if missing && !any_hit then ()
    else begin
      Printf.printf "%-14s" rule;
      List.iter (fun c -> Printf.printf " %4s" c) cells;
      print_newline ()
    end
  ) rules;
  print_newline ();
  let all_covered =
    List.fold_left (fun acc (_, set) -> SS.union acc set) SS.empty suites
  in
  let total = List.length rules in
  let covered = SS.cardinal (SS.filter (fun r -> List.mem r rules) all_covered) in
  let parts = List.map (fun (n, set) ->
    Printf.sprintf "%s=%d" n (SS.cardinal set)) suites in
  Printf.printf "Coverage: %s total=%d/%d\n"
    (String.concat " " parts) covered total

let print_simple ?(missing=false) () =
  let module SS = Set.Make(String) in
  let all_files =
    Suite.all
    |> List.concat_map replays_in
  in
  let counts = Hashtbl.create 64 in
  List.iter (fun f ->
    List.iter (fun r ->
      let n = try Hashtbl.find counts r with Not_found -> 0 in
      Hashtbl.replace counts r (n + 1)) (rules_in_file f)
  ) all_files;
  let rules = all_rules () in
  if missing then begin
    print_endline "Rules with no coverage:";
    List.iter (fun r ->
      if not (Hashtbl.mem counts r) then
        Printf.printf "  %s\n" r) rules
  end else begin
    Printf.printf "%-14s %6s\n" "RULE" "COUNT";
    Printf.printf "%-14s %6s\n" "----" "-----";
    List.iter (fun r ->
      let n = try Hashtbl.find counts r with Not_found -> 0 in
      Printf.printf "%-14s %6d\n" r n
    ) rules
  end;
  let covered =
    Hashtbl.fold (fun _ _ acc -> acc + 1)
      (let h = Hashtbl.create 32 in
       Hashtbl.iter (fun k _ ->
         if List.mem k rules then Hashtbl.replace h k ()) counts;
       h)
      0
  in
  let total = List.length rules in
  Printf.printf "\nCoverage: %d/%d rules\n" covered total
