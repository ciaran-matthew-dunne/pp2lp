(* Lambdapi diagnostic parsing & formatting.
   Replaces bench/format_error.py. Reads `lambdapi check --json` NDJSON
   on stdout (mixed with non-JSON lines on older builds) and surfaces
   the error info in a few user-friendly forms. *)

type loc = {
  file : string;
  line : int;
  col : int;
}

type diag = {
  loc : loc option;
  message : string;
  severity : string; (* "error" | "warning" | ... *)
}

(* Strip ANSI escape sequences from a string. *)
let strip_ansi s =
  let b = Buffer.create (String.length s) in
  let i = ref 0 in
  let n = String.length s in
  while !i < n do
    if !i + 1 < n && s.[!i] = '\x1b' && s.[!i + 1] = '[' then begin
      (* Skip until a letter *)
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

(* Make a path relative to PP2LP_ROOT (or cwd) when it's a prefix. *)
let relativize path =
  let root =
    try Sys.getenv "PP2LP_ROOT"
    with Not_found ->
      try Sys.getcwd () with _ -> ""
  in
  if root <> "" && String.starts_with ~prefix:root path then
    let n = String.length root in
    let rest = String.sub path n (String.length path - n) in
    if String.length rest > 0 && rest.[0] = '/'
    then String.sub rest 1 (String.length rest - 1)
    else rest
  else path

let bind o f = Option.bind o f

let parse_diag obj =
  let kind = bind (Json_out.field "kind" obj) Json_out.as_string
             |> Option.value ~default:""
  in
  if kind <> "diagnostic" then None
  else begin
    let severity =
      bind (Json_out.field "severity" obj) Json_out.as_string
      |> Option.value ~default:""
    in
    let message =
      bind (Json_out.field "message" obj) Json_out.as_string
      |> Option.value ~default:""
    in
    let loc =
      let file =
        bind (Json_out.field "file" obj) Json_out.as_string in
      let range = Json_out.field "range" obj in
      let start = bind range (Json_out.field "start") in
      let line = bind (bind start (Json_out.field "line")) Json_out.as_int in
      let col = bind (bind start (Json_out.field "col")) Json_out.as_int in
      match file, line, col with
      | Some f, Some l, Some c ->
        Some { file = relativize f; line = l; col = c }
      | _ -> None
    in
    Some { loc; message; severity }
  end

(* Parse NDJSON lambdapi output. Returns (diagnostics, raw_text).
   Lines that don't start with '{' are kept in raw_text only. *)
let parse_ndjson (text : string) : diag list * string =
  let raw = Buffer.create (String.length text) in
  let diags = ref [] in
  String.split_on_char '\n' text
  |> List.iter (fun line ->
    let trimmed = String.trim line in
    if String.length trimmed > 0 && trimmed.[0] = '{' then begin
      try
        let v = Json_out.parse_string trimmed in
        match parse_diag v with
        | Some d -> diags := d :: !diags
        | None -> ()
      with Json_out.Parse_error _ ->
        Buffer.add_string raw line;
        Buffer.add_char raw '\n'
    end else begin
      Buffer.add_string raw line;
      Buffer.add_char raw '\n'
    end);
  (List.rev !diags, Buffer.contents raw)

(* Pretty-print errors for the terminal. Mirrors format_error.py:
   - If we have NDJSON errors, show location + message.
   - Otherwise, fall back to ANSI-stripped scan for error-y lines. *)
let format_for_terminal ?(warnings_text="") (text : string) : string =
  let diags, raw = parse_ndjson text in
  let errors = List.filter (fun d -> d.severity = "error") diags in
  let b = Buffer.create 512 in
  if errors <> [] then begin
    List.iter (fun d ->
      let loc = match d.loc with
        | Some l -> Printf.sprintf "%s:%d:%d" l.file l.line l.col
        | None -> "?"
      in
      Buffer.add_string b "  ";
      Buffer.add_string b loc;
      Buffer.add_char b '\n';
      let lines = String.split_on_char '\n' d.message in
      List.iteri (fun i ln ->
        if i = 0 then Buffer.add_string b "  error: "
        else Buffer.add_string b "         ";
        Buffer.add_string b ln;
        Buffer.add_char b '\n') lines
    ) errors
  end else begin
    let stripped = strip_ansi raw in
    let lines = String.split_on_char '\n' stripped in
    let interesting = List.filter (fun ln ->
      let lc = ln in
      let look kw =
        let n = String.length kw in
        let l = String.length lc in
        let rec scan i =
          if i + n > l then false
          else if String.sub lc i n = kw then true
          else scan (i + 1)
        in
        scan 0
      in
      look "error" || look "Error" || look "Cannot" || look "Unknown")
                      lines
    in
    let chosen = if interesting = [] then lines else interesting in
    (* Last 5 *)
    let chosen =
      let n = List.length chosen in
      if n > 5 then List.filteri (fun i _ -> i >= n - 5) chosen
      else chosen
    in
    List.iter (fun ln ->
      let t = String.trim ln in
      if t <> "" then begin
        Buffer.add_string b "  ";
        Buffer.add_string b ln;
        Buffer.add_char b '\n'
      end) chosen
  end;
  if String.trim warnings_text <> "" then begin
    Buffer.add_string b "  warnings:\n";
    let lines = String.split_on_char '\n' warnings_text
                |> List.map String.trim
                |> List.filter (fun s -> s <> "")
    in
    let counts = Hashtbl.create 16 in
    List.iter (fun w ->
      let n = try Hashtbl.find counts w with Not_found -> 0 in
      Hashtbl.replace counts w (n + 1)) lines;
    let order = ref [] in
    List.iter (fun w ->
      if not (List.mem w !order) then order := w :: !order) lines;
    List.iter (fun w ->
      let n = Hashtbl.find counts w in
      Buffer.add_string b "    ";
      Buffer.add_string b w;
      if n > 1 then Buffer.add_string b (Printf.sprintf " (x%d)" n);
      Buffer.add_char b '\n') (List.rev !order)
  end;
  Buffer.contents b

(* Convert a diagnostic to JSON for the --json paths in main.ml. *)
let diag_to_json d =
  let base =
    [ "severity", Json_out.JStr d.severity;
      "message",  Json_out.JStr d.message ] in
  let loc = match d.loc with
    | None -> []
    | Some l -> ["loc", Json_out.JObj
                   [ "file", Json_out.JStr l.file;
                     "line", Json_out.JInt l.line;
                     "col",  Json_out.JInt l.col ]]
  in
  Json_out.JObj (base @ loc)
