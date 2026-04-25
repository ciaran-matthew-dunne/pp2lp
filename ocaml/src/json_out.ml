(* Minimal JSON output. Hand-rolled to avoid pulling in yojson.
   Only what the pp2lp CLI needs to emit. *)

let buf_add_string_escaped buf s =
  Buffer.add_char buf '"';
  String.iter (fun c ->
    match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
      Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c) s;
  Buffer.add_char buf '"'

type t =
  | JNull
  | JBool of bool
  | JInt of int
  | JStr of string
  | JList of t list
  | JObj of (string * t) list

let rec write buf = function
  | JNull -> Buffer.add_string buf "null"
  | JBool true -> Buffer.add_string buf "true"
  | JBool false -> Buffer.add_string buf "false"
  | JInt n -> Buffer.add_string buf (string_of_int n)
  | JStr s -> buf_add_string_escaped buf s
  | JList xs ->
    Buffer.add_char buf '[';
    List.iteri (fun i v ->
      if i > 0 then Buffer.add_char buf ',';
      write buf v) xs;
    Buffer.add_char buf ']'
  | JObj kvs ->
    Buffer.add_char buf '{';
    List.iteri (fun i (k, v) ->
      if i > 0 then Buffer.add_char buf ',';
      buf_add_string_escaped buf k;
      Buffer.add_char buf ':';
      write buf v) kvs;
    Buffer.add_char buf '}'

let to_string j =
  let b = Buffer.create 256 in
  write b j;
  Buffer.contents b

let print_line j =
  print_string (to_string j);
  print_char '\n'

(* Minimal NDJSON line scanner: split on '\n', drop blank, attempt to find
   leading "{" → returns the string line for downstream parsing. *)
let lines s =
  String.split_on_char '\n' s
  |> List.filter (fun l -> String.length l > 0)

(* --- Tiny JSON value parser ---
   Used only to consume lambdapi --json NDJSON, which is well-formed.
   Not fully spec-compliant; supports objects, arrays, strings,
   numbers, true/false/null. Errors raise [Parse_error]. *)

exception Parse_error of string

let parse_string s =
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
      raise (Parse_error (Printf.sprintf "expected %C at pos %d, got %C"
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
    | c -> raise (Parse_error (Printf.sprintf "unexpected %C at %d" c !pos))
  and string_lit () =
    expect '"';
    let b = Buffer.create 32 in
    let rec loop () =
      if !pos >= len then raise (Parse_error "unterminated string");
      match s.[!pos] with
      | '"' -> advance ()
      | '\\' ->
        advance ();
        if !pos >= len then raise (Parse_error "bad escape");
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
           if !pos + 4 > len then raise (Parse_error "bad \\u");
           let hex = String.sub s !pos 4 in
           pos := !pos + 4;
           let code = int_of_string ("0x" ^ hex) in
           (* Encode codepoint as UTF-8. *)
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
         | c -> raise (Parse_error (Printf.sprintf "bad escape \\%c" c)))
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
        | c -> raise (Parse_error (Printf.sprintf
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
        | c -> raise (Parse_error (Printf.sprintf
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
      raise (Parse_error (Printf.sprintf "expected %s at %d" kw !pos));
    pos := !pos + n
  in
  let v = value () in
  skip_ws ();
  v

(* Field accessors. Return None if absent or wrong type. *)

let field k = function
  | JObj kvs -> (try Some (List.assoc k kvs) with Not_found -> None)
  | _ -> None

let as_string = function JStr s -> Some s | _ -> None
let as_int = function JInt n -> Some n | _ -> None
let _as_obj = function JObj _ as v -> Some v | _ -> None
