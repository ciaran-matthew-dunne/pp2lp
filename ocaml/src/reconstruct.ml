(* Top-level: read a `.replay` file → emit a Lambdapi proof string. *)

let is_simple_ident = Pp_lp.is_simple_ident

let name_of_file (fp : string) : string =
  let stem = Filename.remove_extension (Filename.basename fp) in
  if is_simple_ident stem then stem
  else Printf.sprintf "{|%s|}" stem

let goal_of_tree tree =
  match Proof_tree.anno_of tree with
  | Some anno -> Syntax_pp.prd_of_rhs anno
  | None -> failwith "root node of proof tree has no annotation"

let warn_unsupported_rules rules =
  let seen = Hashtbl.create 16 in
  let unsup = List.filter_map (fun ((rule, _arg), _anno) ->
    if Rule_db.is_unsupported rule && not (Rule_db.is_phantom rule)
       && not (Hashtbl.mem seen rule) then begin
      Hashtbl.replace seen rule ();
      Some rule
    end else None
  ) rules in
  match unsup with
  | [] -> ()
  | _ -> Printf.eprintf "WARNING: unsupported rules: %s\n%!" (String.concat ", " unsup)

let reconstruct_file (fp : string) : string =
  let replay = Parse_replay.parse_file fp in
  warn_unsupported_rules replay.rules;
  let tree = Proof_tree.build replay.rules in
  let goal = Syntax_pp.flatten_binds (goal_of_tree tree) in
  Emit_lp.emit_lp (name_of_file fp) goal tree

let reconstruct_symbol (fp : string) : string =
  let replay = Parse_replay.parse_file fp in
  warn_unsupported_rules replay.rules;
  let tree = Proof_tree.build replay.rules in
  let goal = Syntax_pp.flatten_binds (goal_of_tree tree) in
  Emit_lp.emit_symbol (name_of_file fp) goal tree
