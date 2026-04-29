(* Lambdapi diagnostic parsing & formatting. Reads `lambdapi check
   --json` NDJSON on stdout (mixed with non-JSON lines on older builds)
   and surfaces error info for the terminal. *)

(* ---- Minimal JSON parser (private). Just enough for lambdapi's
   NDJSON; not spec-compliant. Supports objects, arrays, strings,
   numbers, true/false/null. *)

type json =
  | JNull
  | JBool of bool
  | JInt of int
  | JStr of string
  | JList of json list
  | JObj of (string * json) list

exception Json_parse of string

let parse_json s =
  let pos = ref 0 in
  let len = String.length s in
  let peek () = if !pos >= len then '\000' else s.[!pos] in
  let advance () = incr pos in
  let skip_ws () =
    while !pos < len &&
          (s.[!pos] = ' ' || s.[!pos] = '\t' ||
           s.[!pos] = '\n' || s.[!pos] = '\r')
    do incr pos done
  in
  let expect c =
    if peek () <> c then
      raise (Json_parse (Printf.sprintf "expected %C at pos %d, got %C"
                           c !pos (peek ())));
    advance ()
  in
  let rec value () =
    skip_ws ();
    match peek () with
    | '"' -> JStr (string_lit ())
    | '{' -> obj ()
    | '[' -> arr ()
    | 't' -> consume "true"; JBool true
    | 'f' -> consume "false"; JBool false
    | 'n' -> consume "null"; JNull
    | c when c = '-' || (c >= '0' && c <= '9') -> num ()
    | c -> raise (Json_parse (Printf.sprintf "unexpected %C at %d" c !pos))
  and string_lit () =
    expect '"';
    let b = Buffer.create 32 in
    let rec loop () =
      if !pos >= len then raise (Json_parse "unterminated string");
      match s.[!pos] with
      | '"' -> advance ()
      | '\\' ->
        advance ();
        if !pos >= len then raise (Json_parse "bad escape");
        (match s.[!pos] with
         | '"' -> Buffer.add_char b '"'; advance (); loop ()
         | '\\' -> Buffer.add_char b '\\'; advance (); loop ()
         | '/' -> Buffer.add_char b '/'; advance (); loop ()
         | 'n' -> Buffer.add_char b '\n'; advance (); loop ()
         | 'r' -> Buffer.add_char b '\r'; advance (); loop ()
         | 't' -> Buffer.add_char b '\t'; advance (); loop ()
         | 'b' -> Buffer.add_char b '\b'; advance (); loop ()
         | 'f' -> Buffer.add_char b '\012'; advance (); loop ()
         | 'u' ->
           advance ();
           if !pos + 4 > len then raise (Json_parse "bad \\u");
           let hex = String.sub s !pos 4 in
           pos := !pos + 4;
           let code = int_of_string ("0x" ^ hex) in
           if code < 0x80 then
             Buffer.add_char b (Char.chr code)
           else if code < 0x800 then begin
             Buffer.add_char b (Char.chr (0xC0 lor (code lsr 6)));
             Buffer.add_char b (Char.chr (0x80 lor (code land 0x3F)))
           end else begin
             Buffer.add_char b (Char.chr (0xE0 lor (code lsr 12)));
             Buffer.add_char b (Char.chr (0x80 lor ((code lsr 6) land 0x3F)));
             Buffer.add_char b (Char.chr (0x80 lor (code land 0x3F)))
           end;
           loop ()
         | c -> raise (Json_parse (Printf.sprintf "bad escape \\%c" c)))
      | c -> Buffer.add_char b c; advance (); loop ()
    in
    loop ();
    Buffer.contents b
  and obj () =
    expect '{';
    skip_ws ();
    let kvs = ref [] in
    if peek () = '}' then (advance (); JObj [])
    else begin
      let rec loop () =
        skip_ws ();
        let k = string_lit () in
        skip_ws (); expect ':';
        let v = value () in
        kvs := (k, v) :: !kvs;
        skip_ws ();
        match peek () with
        | ',' -> advance (); loop ()
        | '}' -> advance ()
        | c -> raise (Json_parse (Printf.sprintf
                                    "expected ',' or '}' got %C at %d" c !pos))
      in
      loop ();
      JObj (List.rev !kvs)
    end
  and arr () =
    expect '[';
    skip_ws ();
    let xs = ref [] in
    if peek () = ']' then (advance (); JList [])
    else begin
      let rec loop () =
        let v = value () in
        xs := v :: !xs;
        skip_ws ();
        match peek () with
        | ',' -> advance (); loop ()
        | ']' -> advance ()
        | c -> raise (Json_parse (Printf.sprintf
                                    "expected ',' or ']' got %C at %d" c !pos))
      in
      loop ();
      JList (List.rev !xs)
    end
  and num () =
    let start = !pos in
    if peek () = '-' then advance ();
    while !pos < len &&
          ((s.[!pos] >= '0' && s.[!pos] <= '9') ||
           s.[!pos] = '.' || s.[!pos] = 'e' || s.[!pos] = 'E' ||
           s.[!pos] = '+' || s.[!pos] = '-')
    do incr pos done;
    let lit = String.sub s start (!pos - start) in
    (try JInt (int_of_string lit)
     with _ -> JStr lit)
  and consume kw =
    let n = String.length kw in
    if !pos + n > len || String.sub s !pos n <> kw then
      raise (Json_parse (Printf.sprintf "expected %s at %d" kw !pos));
    pos := !pos + n
  in
  let v = value () in
  skip_ws ();
  v

let field k = function
  | JObj kvs -> (try Some (List.assoc k kvs) with Not_found -> None)
  | _ -> None

let as_string = function JStr s -> Some s | _ -> None
let as_int = function JInt n -> Some n | _ -> None

(* ---- Diagnostics ---- *)

type loc = { file : string; line : int; col : int }
type diag = { loc : loc option; message : string; severity : string }

let strip_ansi s =
  let b = Buffer.create (String.length s) in
  let i = ref 0 in
  let n = String.length s in
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

let relativize path =
  let root =
    try Sys.getenv "PP2LP_ROOT"
    with Not_found -> try Sys.getcwd () with _ -> ""
  in
  if root <> "" && String.starts_with ~prefix:root path then
    let n = String.length root in
    let rest = String.sub path n (String.length path - n) in
    if String.length rest > 0 && rest.[0] = '/'
    then String.sub rest 1 (String.length rest - 1)
    else rest
  else path

let bind = Option.bind

let parse_diag obj =
  let kind = bind (field "kind" obj) as_string |> Option.value ~default:"" in
  if kind <> "diagnostic" then None
  else
    let severity = bind (field "severity" obj) as_string |> Option.value ~default:"" in
    let message = bind (field "message" obj) as_string |> Option.value ~default:"" in
    let loc =
      let file = bind (field "file" obj) as_string in
      let range = field "range" obj in
      let start = bind range (field "start") in
      let line = bind (bind start (field "line")) as_int in
      let col = bind (bind start (field "col")) as_int in
      match file, line, col with
      | Some f, Some l, Some c -> Some { file = relativize f; line = l; col = c }
      | _ -> None
    in
    Some { loc; message; severity }

let parse_ndjson (text : string) : diag list * string =
  let raw = Buffer.create (String.length text) in
  let diags = ref [] in
  String.split_on_char '\n' text
  |> List.iter (fun line ->
    let trimmed = String.trim line in
    if String.length trimmed > 0 && trimmed.[0] = '{' then begin
      try
        let v = parse_json trimmed in
        match parse_diag v with
        | Some d -> diags := d :: !diags
        | None -> ()
      with Json_parse _ ->
        Buffer.add_string raw line;
        Buffer.add_char raw '\n'
    end else begin
      Buffer.add_string raw line;
      Buffer.add_char raw '\n'
    end);
  (List.rev !diags, Buffer.contents raw)

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
      let look kw =
        let n = String.length kw in
        let l = String.length ln in
        let rec scan i =
          if i + n > l then false
          else if String.sub ln i n = kw then true
          else scan (i + 1)
        in
        scan 0
      in
      look "error" || look "Error" || look "Cannot" || look "Unknown") lines
    in
    let chosen = if interesting = [] then lines else interesting in
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
