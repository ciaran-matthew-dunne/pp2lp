(* Rule database: single source of truth for PP inference rule metadata.
   Loaded from data/rules.json at startup. *)

type rule_info = {
  name: string;
  section: string option;
  arity: int;
  primed: bool;
  result_schema: int option;  (* 0=leaf/TRUE, 1=passthrough, 2=conjunction *)
  emit_args: string option;   (* static args or "dynamic:tag" *)
  lp_file: string option;
  lp_status: string;          (* "proved" | "admitted" | "todo" | "phantom" *)
}

type emit_variant = {
  base: string;
  variant: string;
  condition: string;
}

type flat_suffix = {
  fs_base: string;
  flat_name: string;
}

type db = {
  rules: rule_info list;
  by_name: (string, rule_info) Hashtbl.t;
  emit_variants: emit_variant list;
  flat_suffixes: flat_suffix list;
}

(* JSON helpers *)
let member key json =
  match json with
  | `Assoc l -> (try List.assoc key l with Not_found -> `Null)
  | _ -> `Null

let to_string_opt = function `String s -> Some s | _ -> None
let to_string = function `String s -> s | _ -> failwith "expected string"
let to_int = function `Int n -> n | _ -> failwith "expected int"
let to_int_opt = function `Int n -> Some n | _ -> None
let to_bool = function `Bool b -> b | _ -> failwith "expected bool"
let to_list = function `List l -> l | _ -> failwith "expected list"

let parse_rule json =
  { name = to_string (member "name" json);
    section = to_string_opt (member "section" json);
    arity = to_int (member "arity" json);
    primed = to_bool (member "primed" json);
    result_schema = to_int_opt (member "result_schema" json);
    emit_args = to_string_opt (member "emit_args" json);
    lp_file = to_string_opt (member "lp_file" json);
    lp_status = to_string (member "lp_status" json);
  }

let parse_emit_variant json =
  { base = to_string (member "base" json);
    variant = to_string (member "variant" json);
    condition = to_string (member "condition" json);
  }

let parse_flat_suffix json =
  { fs_base = to_string (member "base" json);
    flat_name = to_string (member "flat_name" json);
  }

let to_list_or_empty = function `List l -> l | _ -> []

let load path =
  let json = Yojson.Basic.from_file path in
  let rules = List.map parse_rule (to_list (member "rules" json)) in
  let by_name = Hashtbl.create (List.length rules) in
  List.iter (fun r -> Hashtbl.replace by_name r.name r) rules;
  (* Also register flat suffixes and emit variants as lookupable *)
  let flat_suffixes =
    List.map parse_flat_suffix (to_list_or_empty (member "flat_suffixes" json))
  in
  List.iter (fun fs ->
    match Hashtbl.find_opt by_name fs.fs_base with
    | Some base_rule ->
      Hashtbl.replace by_name fs.flat_name
        { base_rule with name = fs.flat_name }
    | None ->
      Printf.eprintf "warning: flat_suffix %S references unknown base rule %S\n"
        fs.flat_name fs.fs_base
  ) flat_suffixes;
  let emit_variants =
    List.map parse_emit_variant (to_list_or_empty (member "emit_variants" json))
  in
  (* Register emit variants as lookupable (inherit base rule's metadata) *)
  List.iter (fun ev ->
    match Hashtbl.find_opt by_name ev.base with
    | Some base_rule ->
      if not (Hashtbl.mem by_name ev.variant) then
        Hashtbl.replace by_name ev.variant
          { base_rule with name = ev.variant }
    | None ->
      Printf.eprintf "warning: emit_variant %S references unknown base rule %S\n"
        ev.variant ev.base
  ) emit_variants;
  { rules; by_name; emit_variants; flat_suffixes }

(* --- Lookup functions (replace proof_tree.ml / emit_lp.ml metadata) --- *)

let find db name = Hashtbl.find_opt db.by_name name

let rule_arity db name =
  match find db name with
  | Some r -> r.arity
  | None ->
    Printf.eprintf "warning: unknown rule %S, assuming arity 1\n" name;
    1

let has_primed db name =
  match find db name with
  | Some r -> r.primed
  | None ->
    Printf.eprintf "warning: unknown rule %S, assuming no primed variant\n" name;
    false

let emit_args db name =
  match find db name with
  | Some r -> r.emit_args
  | None -> None

let lp_status db name =
  match find db name with
  | Some r -> r.lp_status
  | None ->
    Printf.eprintf "warning: unknown rule %S, status unknown\n" name;
    "unknown"

(* --- Global instance --- *)

let global_db : db option ref = ref None

let init path =
  global_db := Some (load path)

let get () =
  match !global_db with
  | Some db -> db
  | None -> failwith "Rule_db not initialised: call Rule_db.init first"

(* Convenience: find the rules.json relative to the executable or project root *)
let find_rules_json () =
  let candidates = [
    "data/rules.json";
    "../data/rules.json";
    "../../data/rules.json";
    "../../../data/rules.json";
  ] in
  List.find_opt Sys.file_exists candidates

let auto_init () =
  match !global_db with
  | Some _ -> ()  (* already loaded *)
  | None ->
    match find_rules_json () with
    | Some path -> init path
    | None -> failwith "Cannot find data/rules.json"
