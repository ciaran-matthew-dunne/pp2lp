(* File-level Lambdapi tooling — no LSP dependency.
   Used by `pp2lp lp-axioms` (and friends) to scan .lp files for
   declarations, rewrite rules, and admits without spinning up the
   LSP server. The LSP-backed tools (goals/try/query/proofterm/symbols)
   stay in the lambdapi-mcp Python repo. *)

(* --- comment stripping ---
   Replace each comment with whitespace of the same length so 1-based
   line numbers and per-line offsets stay aligned. *)

let strip_comments (s : string) : string =
  let n = String.length s in
  let b = Bytes.of_string s in
  let i = ref 0 in
  while !i < n do
    if !i + 1 < n && Bytes.get b !i = '/' && Bytes.get b (!i + 1) = '/' then begin
      (* Line comment: blank to end of line. *)
      let j = ref !i in
      while !j < n && Bytes.get b !j <> '\n' do
        Bytes.set b !j ' '; incr j
      done;
      i := !j
    end
    else if !i + 1 < n && Bytes.get b !i = '/' && Bytes.get b (!i + 1) = '*' then begin
      let j = ref (!i + 2) in
      Bytes.set b !i ' '; Bytes.set b (!i + 1) ' ';
      let closed = ref false in
      while !j < n - 1 && not !closed do
        if Bytes.get b !j = '*' && Bytes.get b (!j + 1) = '/' then begin
          Bytes.set b !j ' '; Bytes.set b (!j + 1) ' ';
          j := !j + 2; closed := true
        end else begin
          if Bytes.get b !j <> '\n' then Bytes.set b !j ' ';
          incr j
        end
      done;
      if not !closed then begin
        (* Unterminated /* — blank rest of file. *)
        while !j < n do
          if Bytes.get b !j <> '\n' then Bytes.set b !j ' ';
          incr j
        done
      end;
      i := !j
    end
    else incr i
  done;
  Bytes.to_string b

(* --- statement splitter ---
   Split text at top-level `;`. Tracks open-paren / open-bracket depth
   so e.g. `f(x;y)` doesn't split. Returns (start_line_1based, body)
   pairs. Blank statements skipped. *)

let split_statements (text : string) : (int * string) list =
  let n = String.length text in
  let acc = ref [] in
  let buf = Buffer.create 128 in
  let depth = ref 0 in
  let line = ref 1 in
  let stmt_start = ref None in
  for i = 0 to n - 1 do
    let c = text.[i] in
    if c <> ' ' && c <> '\t' && c <> '\n' && !stmt_start = None then
      stmt_start := Some !line;
    (match c with
     | '(' | '[' | '{' -> incr depth
     | ')' | ']' | '}' -> decr depth
     | _ -> ());
    if c = ';' && !depth = 0 then begin
      let body = String.trim (Buffer.contents buf) in
      (match !stmt_start with
       | Some s when body <> "" -> acc := (s, body) :: !acc
       | _ -> ());
      Buffer.clear buf;
      stmt_start := None
    end else
      Buffer.add_char buf c;
    if c = '\n' then incr line
  done;
  List.rev !acc

(* --- symbol declaration recogniser ---
   Match (after comment strip + whitespace normalisation):
     [private|protected|sequential|injective|opaque ...]*
     [constant ]symbol NAME [BINDERS] : TYPE
   Body has NO `≔` (otherwise it's a definition, not an assumption).

   We don't try to parse the binder list — we just find the `:` *after*
   the symbol name (not inside parens), then take the rest as type.

   Returns Some (name, type_str, is_constant) or None. *)

let modifier_words =
  ["private"; "protected"; "sequential"; "injective"; "opaque";
   "associative"; "commutative"; "left"; "right"]

(* Try to consume a leading word from [s] starting at [pos]; return
   None if the word doesn't match any of [words]. *)
let try_consume_word ~words s pos =
  let n = String.length s in
  let rec skip_ws p = if p < n && (s.[p] = ' ' || s.[p] = '\t') then skip_ws (p+1) else p in
  let p = skip_ws pos in
  let q = ref p in
  while !q < n && let c = s.[!q] in (c >= 'a' && c <= 'z') do incr q done;
  if !q = p then None
  else
    let w = String.sub s p (!q - p) in
    if List.mem w words then Some (w, !q) else None

let parse_symbol_decl (stmt : string) : (string * string * bool) option =
  let s = String.concat " "
            (List.filter (fun w -> w <> "")
               (String.split_on_char ' '
                  (String.map (fun c ->
                     if c = '\n' || c = '\t' then ' ' else c) stmt))) in
  let n = String.length s in
  let pos = ref 0 in
  (* Skip modifiers *)
  let rec skip_mods () =
    match try_consume_word ~words:modifier_words s !pos with
    | Some (_, p') -> pos := p'; skip_mods ()
    | None -> ()
  in
  skip_mods ();
  (* Optional `constant` *)
  let is_constant =
    match try_consume_word ~words:["constant"] s !pos with
    | Some (_, p') -> pos := p'; true
    | None -> false
  in
  (* Required `symbol` *)
  match try_consume_word ~words:["symbol"] s !pos with
  | None -> None
  | Some (_, p') ->
    pos := p';
    (* Skip whitespace *)
    while !pos < n && (s.[!pos] = ' ' || s.[!pos] = '\t') do incr pos done;
    (* Capture name: first run of non-space, non-`:`, non-`(`, non-`[` chars *)
    let name_start = !pos in
    while !pos < n &&
          let c = s.[!pos] in
          c <> ' ' && c <> '\t' && c <> ':' && c <> '(' && c <> '['
    do incr pos done;
    if !pos = name_start then None
    else begin
      let name = String.sub s name_start (!pos - name_start) in
      (* Locate top-level `:` after binders. Track paren/bracket depth. *)
      let depth = ref 0 in
      let colon = ref (-1) in
      let k = ref !pos in
      while !k < n && !colon = -1 do
        let c = s.[!k] in
        (match c with
         | '(' | '[' -> incr depth
         | ')' | ']' -> decr depth
         | ':' when !depth = 0 ->
           (* Skip ":=" (Lambdapi uses it for definitions). *)
           if !k + 1 < n && s.[!k + 1] = '=' then incr k
           else colon := !k
         | _ -> ());
        incr k
      done;
      if !colon = -1 then None
      else begin
        let type_str = String.trim (String.sub s (!colon + 1) (n - !colon - 1)) in
        Some (name, type_str, is_constant)
      end
    end

(* `≔` is U+2254 = three bytes E2 89 94. ":=" also defines. *)
let has_definition_body (stmt : string) : bool =
  let n = String.length stmt in
  let i = ref 0 in
  let found = ref false in
  while !i < n && not !found do
    if !i + 2 < n
       && Char.code stmt.[!i] = 0xE2
       && Char.code stmt.[!i + 1] = 0x89
       && Char.code stmt.[!i + 2] = 0x94
    then found := true
    else if !i + 1 < n && stmt.[!i] = ':' && stmt.[!i + 1] = '=' then
      found := true
    else incr i
  done;
  !found

(* Propositional iff the type starts with `π` (U+03C0, two bytes CF 80)
   or contains a top-level `Π …, π …`. We approximate: leading π or
   `, π` / ` π` / `(π` somewhere. *)
let is_propositional (type_str : string) : bool =
  let n = String.length type_str in
  let starts_with_pi i =
    i + 1 < n &&
    Char.code type_str.[i] = 0xCF && Char.code type_str.[i + 1] = 0x80
  in
  if starts_with_pi 0 then true
  else
    let rec scan i =
      if i + 1 >= n then false
      else if starts_with_pi i &&
              (let prev = type_str.[i - 1] in
               prev = ' ' || prev = '\t' || prev = ',' || prev = '(')
      then true
      else scan (i + 1)
    in
    scan 1

(* --- rewrite rules ---
   `rule LHS ↪ RHS [with LHS' ↪ RHS']*;`
   We split on top-level `with`, then on `↪` (UTF-8 E2 86 AA).
   For the head symbol: leading identifier on the LHS. *)

(* Split [body] on top-level `with` (depth 0). Returns substrings. *)
let split_on_with_top (body : string) : string list =
  let n = String.length body in
  let acc = ref [] in
  let buf = Buffer.create 64 in
  let depth = ref 0 in
  let i = ref 0 in
  let is_word_char c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
    (c >= '0' && c <= '9') || c = '_'
  in
  while !i < n do
    let c = body.[!i] in
    (match c with
     | '(' | '[' | '{' -> incr depth
     | ')' | ']' | '}' -> decr depth
     | _ -> ());
    if !depth = 0
       && !i + 4 <= n
       && String.sub body !i 4 = "with"
       && (!i = 0 || not (is_word_char body.[!i - 1]))
       && (!i + 4 = n || not (is_word_char body.[!i + 4]))
    then begin
      acc := Buffer.contents buf :: !acc;
      Buffer.clear buf;
      i := !i + 4
    end else begin
      Buffer.add_char buf c;
      incr i
    end
  done;
  acc := Buffer.contents buf :: !acc;
  List.rev !acc

(* Split a single sub-rule on `↪` (U+21AA, three bytes E2 86 AA).
   Returns (lhs, rhs) or None. *)
let split_on_arrow (sub : string) : (string * string) option =
  let n = String.length sub in
  let i = ref 0 in
  let found = ref (-1) in
  while !i + 2 < n && !found = -1 do
    if Char.code sub.[!i] = 0xE2
       && Char.code sub.[!i + 1] = 0x86
       && Char.code sub.[!i + 2] = 0xAA
    then found := !i
    else incr i
  done;
  if !found = -1 then None
  else
    let lhs = String.trim (String.sub sub 0 !found) in
    let rhs =
      String.trim (String.sub sub (!found + 3) (n - !found - 3))
    in
    Some (lhs, rhs)

let head_of_lhs (lhs : string) : string =
  let n = String.length lhs in
  let i = ref 0 in
  while !i < n && (lhs.[!i] = ' ' || lhs.[!i] = '\t') do incr i done;
  let start = !i in
  while !i < n &&
        let c = lhs.[!i] in
        c <> ' ' && c <> '\t' && c <> '(' && c <> '['
  do incr i done;
  if !i = start then "" else String.sub lhs start (!i - start)

(* --- top-level scan ---
   For one .lp file, returns three lists: assumptions, rewrite_rules,
   admits. Locations are 1-based line numbers in the *original* file
   (comment-stripping preserves newlines so they line up). *)

type assumption = {
  a_file : string;
  a_line : int;
  name : string;
  type_ : string;
  propositional : bool;
  constant : bool;
}

type rewrite_rule = {
  r_file : string;
  r_line : int;
  symbol : string;
  lhs : string;
  rhs : string;
}

type admit_loc = { d_file : string; d_line : int }

(* Match a leading "rule " keyword. *)
let starts_with_rule (stmt : string) : string option =
  let n = String.length stmt in
  let i = ref 0 in
  while !i < n && (stmt.[!i] = ' ' || stmt.[!i] = '\t') do incr i done;
  if !i + 5 <= n && String.sub stmt !i 4 = "rule"
     && (!i + 4 = n ||
         let c = stmt.[!i + 4] in
         not ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
              (c >= '0' && c <= '9') || c = '_'))
  then Some (String.sub stmt (!i + 4) (n - !i - 4))
  else None

let read_file_text path =
  let ic = open_in path in
  let s = In_channel.input_all ic in
  close_in ic;
  s

let scan_file (path : string) :
  assumption list * rewrite_rule list * admit_loc list =
  let raw = read_file_text path in
  let stripped = strip_comments raw in
  let stmts = split_statements stripped in
  let assumptions = ref [] in
  let rules = ref [] in
  let admits = ref [] in
  List.iter (fun (line, stmt) ->
    match starts_with_rule stmt with
    | Some body ->
      List.iter (fun sub ->
        match split_on_arrow sub with
        | None -> ()
        | Some (lhs, rhs) ->
          let head = head_of_lhs lhs in
          let norm s = String.concat " "
              (List.filter (fun w -> w <> "")
                 (String.split_on_char ' '
                    (String.map (fun c ->
                       if c = '\n' || c = '\t' then ' ' else c) s)))
          in
          rules := { r_file = path; r_line = line; symbol = head;
                     lhs = norm lhs; rhs = norm rhs } :: !rules
      ) (split_on_with_top body)
    | None ->
      if has_definition_body stmt then ()
      else
        match parse_symbol_decl stmt with
        | None -> ()
        | Some (name, type_, is_constant) ->
          assumptions := { a_file = path; a_line = line;
                           name; type_;
                           propositional = is_propositional type_;
                           constant = is_constant } :: !assumptions
  ) stmts;
  (* Admits: scan original text line by line. `\badmit\b`. Comment-
     stripped text preserves line numbers. *)
  let lines = String.split_on_char '\n' stripped in
  List.iteri (fun i line ->
    let n = String.length line in
    let is_word_char c =
      (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
      (c >= '0' && c <= '9') || c = '_'
    in
    let j = ref 0 in
    let hit = ref false in
    while !j + 5 <= n && not !hit do
      if String.sub line !j 5 = "admit"
         && (!j = 0 || not (is_word_char line.[!j - 1]))
         && (!j + 5 = n || not (is_word_char line.[!j + 5]))
      then hit := true
      else incr j
    done;
    if !hit then admits := { d_file = path; d_line = i + 1 } :: !admits
  ) lines;
  (List.rev !assumptions, List.rev !rules, List.rev !admits)

(* --- require parsing ---
   `require [open] <module>[, <module>]* ;`
   We extract the module-name tokens (dot-separated identifiers) from
   each require statement. *)

let parse_requires (stmt : string) : string list =
  let n = String.length stmt in
  let i = ref 0 in
  while !i < n && (stmt.[!i] = ' ' || stmt.[!i] = '\t' || stmt.[!i] = '\n')
  do incr i done;
  let consume_word w =
    let wl = String.length w in
    if !i + wl <= n && String.sub stmt !i wl = w
       && (!i + wl = n ||
           let c = stmt.[!i + wl] in
           not ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                (c >= '0' && c <= '9') || c = '_'))
    then begin i := !i + wl; true end else false
  in
  if not (consume_word "require") then []
  else begin
    while !i < n && (stmt.[!i] = ' ' || stmt.[!i] = '\t') do incr i done;
    let _ : bool = consume_word "open" in
    let acc = ref [] in
    let buf = Buffer.create 32 in
    let flush () =
      let s = Buffer.contents buf in
      Buffer.clear buf;
      if s <> "" then acc := s :: !acc
    in
    while !i < n do
      let c = stmt.[!i] in
      if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
         (c >= '0' && c <= '9') || c = '_' || c = '.'
      then Buffer.add_char buf c
      else flush ();
      incr i
    done;
    flush ();
    List.rev !acc
  end

(* --- package discovery ---
   Walk upward from each anchor file looking for lambdapi.pkg, then
   walk downward under the project root for any others. We do NOT
   read $OPAM_SWITCH_PREFIX/lib/lambdapi/lib_root — pp2lp's project
   scope deliberately stops at the project boundary. *)

let read_pkg_file path : (string * string) list =
  try
    let ic = open_in path in
    let acc = ref [] in
    (try while true do
      let l = input_line ic in
      let l = String.trim l in
      if l <> "" && l.[0] <> '#' then begin
        match String.index_opt l '=' with
        | Some i ->
          let k = String.trim (String.sub l 0 i) in
          let v = String.trim (String.sub l (i + 1) (String.length l - i - 1)) in
          acc := (k, v) :: !acc
        | None -> ()
      end
    done with End_of_file -> ());
    close_in ic;
    !acc
  with _ -> []

let dir_of path =
  if Sys.is_directory path then path else Filename.dirname path

(* Walk upward from each anchor to gather (root_path, dir) pairs. *)
let discover_pkg_roots ?(extra_dirs=[]) anchors =
  let roots = Hashtbl.create 8 in
  let add ~dir ~root_path =
    if not (Hashtbl.mem roots root_path) then
      Hashtbl.replace roots root_path dir
  in
  let walk_up start_dir =
    let d = ref (Filename.concat start_dir "") in
    let prev = ref "" in
    while !d <> "" && !d <> !prev do
      let pkg = Filename.concat !d "lambdapi.pkg" in
      if Cache.exists pkg then begin
        let kvs = read_pkg_file pkg in
        match List.assoc_opt "root_path" kvs with
        | Some rp -> add ~dir:!d ~root_path:rp
        | None -> ()
      end;
      prev := !d;
      d := Filename.dirname !d
    done
  in
  List.iter (fun anchor ->
    walk_up (dir_of anchor)
  ) anchors;
  List.iter (fun d -> walk_up d) extra_dirs;
  roots

(* --- probe files ---
   Insert one or more lines into a copy of [original] (sibling file in
   the same directory, so package resolution still works), run a
   callback on the probe path, then unconditionally clean up.

   [insertions] is a list of (line_1based, content) pairs. Lines are
   inserted BEFORE the existing line at that position; multiple
   insertions are sorted and applied in one pass so later positions
   stay aligned with the original numbering. *)

let read_lines path =
  let ic = open_in path in
  let acc = ref [] in
  (try while true do
    acc := input_line ic :: !acc
  done with End_of_file -> ());
  close_in ic;
  List.rev !acc

let write_lines path lines =
  let oc = open_out path in
  let n = List.length lines in
  List.iteri (fun i l ->
    output_string oc l;
    if i < n - 1 then output_char oc '\n'
  ) lines;
  close_out oc

let apply_insertions (lines : string list) (insertions : (int * string) list)
    : string list * (int * string) list =
  (* Returns (new_lines, mapping). Each mapping entry is (probe_line,
     content) — the 1-based line at which `content` ended up in the
     probe file. Insertions at line L mean "becomes the new line L"
     (existing line L shifts down). Insertions past EOF are appended. *)
  let pending = ref (List.stable_sort
                       (fun (a, _) (b, _) -> compare a b) insertions) in
  let out = ref [] in
  let mapping = ref [] in
  let probe_idx = ref 0 in
  let cur = ref 1 in
  List.iter (fun line ->
    while !pending <> [] && fst (List.hd !pending) <= !cur do
      let (_, c) = List.hd !pending in
      pending := List.tl !pending;
      incr probe_idx;
      out := c :: !out;
      mapping := (!probe_idx, c) :: !mapping
    done;
    incr probe_idx;
    out := line :: !out;
    incr cur
  ) lines;
  List.iter (fun (_, c) ->
    incr probe_idx;
    out := c :: !out;
    mapping := (!probe_idx, c) :: !mapping
  ) !pending;
  (List.rev !out, List.rev !mapping)

(* Probe-file naming: keep it in the same directory as the original so
   `require` resolution is unchanged. Use `_pp2lp_probe_<stem>_<pid>.lp`
   so the name is unique (multiple concurrent probes won't collide) and
   easy to spot if cleanup ever fails. *)
let probe_path_for ~original =
  let dir = Filename.dirname original in
  let base = Filename.basename original in
  let stem = try Filename.chop_extension base with _ -> base in
  Filename.concat dir
    (Printf.sprintf "_pp2lp_probe_%s_%d.lp" stem (Unix.getpid ()))

(* Returns (probe_path, mapping). Caller wraps in Fun.protect to clean up. *)
let make_probe ~original ~insertions =
  let probe = probe_path_for ~original in
  let lines = read_lines original in
  let new_lines, mapping = apply_insertions lines insertions in
  write_lines probe new_lines;
  (probe, mapping)

let cleanup_probe probe =
  (try Unix.unlink probe with _ -> ());
  (try Unix.unlink (Filename.chop_extension probe ^ ".lpo") with _ -> ())

(* --- ANSI stripping (also in Lp_diag, repeated locally to avoid the dep) --- *)
let strip_ansi_local (s : string) : string =
  let n = String.length s in
  let b = Buffer.create n in
  let i = ref 0 in
  while !i < n do
    if !i + 1 < n && s.[!i] = '\x1b' && s.[!i + 1] = '[' then begin
      i := !i + 2;
      while !i < n &&
            not (let c = s.[!i] in
                 (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'))
      do incr i done;
      if !i < n then incr i
    end else begin
      Buffer.add_char b s.[!i];
      incr i
    end
  done;
  Buffer.contents b

(* --- output region slicing ---
   Two reliable boundaries in lambdapi output:
     1. `Start checking "..."` and `End checking "..."` — wrap the whole
        elaboration. Anything between is our session.
     2. Top-level commands like `debug +u`, `debug -u`, `verbose 3` are
        echoed as plain text on their own line.

   Location markers (`/path/file.lp:LINE:COL-COL`, ANSI-wrapped) appear
   for some commands (compute/type/print of a symbol, errors) but NOT
   for all (notably, in-proof tactics like `print;` / `proofterm;`).
   So slicing on locations alone is unreliable; we do it best-effort
   only when we can confirm a marker for our probe line. *)

(* Extract the body between `Start checking "..."` and `End checking
   "..."` lines (after ANSI strip). If neither is present, returns the
   text unchanged. *)
let between_session_markers (text : string) : string =
  let lines = String.split_on_char '\n' text in
  let stripped = List.map strip_ansi_local lines in
  let is_start s =
    String.starts_with ~prefix:"Start checking" (String.trim s) in
  let is_end s =
    String.starts_with ~prefix:"End checking" (String.trim s) in
  let inside = ref false in
  let acc = ref [] in
  List.iter2 (fun raw stripped_l ->
    if is_start stripped_l then inside := true
    else if is_end stripped_l then inside := false
    else if !inside then acc := raw :: !acc
  ) lines stripped;
  if !acc = [] then String.trim text
  else String.trim (String.concat "\n" (List.rev !acc))

(* Slice between two literal toggle commands appearing as plain-text
   echoes in lambdapi output. The toggles are inserted by [lp-debug] as
   `debug +FLAGS` / `debug -FLAGS`; they print as bare lines (not ANSI-
   wrapped). Returns the trace between the two echoes, trimmed. *)
(* Best-effort slice for a single probe at a known probe-file line.
   Looks for a location marker `<probe>:LINE:` and slices from there to
   the next location marker. If no marker fires (some commands emit
   bare output), returns "" so the caller can fall back. *)
let slice_at_probe_line ~probe_path ~probe_line (text : string) : string =
  let lines = String.split_on_char '\n' text in
  let probe_basename = Filename.basename probe_path in
  let stripped = List.map strip_ansi_local lines in
  let parse_loc l =
    let n = String.length l in
    let rec find i =
      if i + String.length probe_basename + 1 > n then -1
      else if String.sub l i (String.length probe_basename) = probe_basename
              && l.[i + String.length probe_basename] = ':'
      then i
      else find (i + 1)
    in
    let pos = find 0 in
    if pos < 0 then None
    else
      let after = pos + String.length probe_basename + 1 in
      let j = ref after in
      while !j < n && l.[!j] >= '0' && l.[!j] <= '9' do incr j done;
      if !j > after then
        try Some (int_of_string (String.sub l after (!j - after)))
        with _ -> None
      else None
  in
  let acc = ref [] in
  let started = ref false in
  let stopped = ref false in
  List.iter2 (fun raw stripped_l ->
    if !stopped then ()
    else match parse_loc stripped_l with
      | Some n when n = probe_line -> started := true
      | Some _ when !started -> stopped := true
      | _ -> if !started then acc := raw :: !acc
  ) lines stripped;
  String.trim (String.concat "\n" (List.rev !acc))

let resolve_module ~roots (m : string) : string option =
  let parts = String.split_on_char '.' m in
  match parts with
  | [] -> None
  | head :: rest ->
    match Hashtbl.find_opt roots head with
    | None -> None
    | Some dir ->
      let rel = match rest with
        | [] -> head ^ ".lp"
        | _ -> String.concat Filename.dir_sep rest ^ ".lp"
      in
      let path = Filename.concat dir rel in
      if Cache.exists path then Some path else None
