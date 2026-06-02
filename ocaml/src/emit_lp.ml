open Syntax_pp

let lp_header = "require open pp2lp.B pp2lp.Rules;\n"

let emit_symbol (name : string) (goal : prd) (pp_tree : Proof_tree.pp_tree)
    : string * (int * Lp_tree.prov) list =
  let buf = Buffer.create 4096 in
  (* Header in the same buffer so the sink's line numbers are file-absolute. *)
  Buffer.add_string buf lp_header;
  Buffer.add_char buf '\n';
  let fv = Free_vars.free_vars_of_prd goal in
  let prop_list = Free_vars.SS.elements fv.prop_vars in
  let exp_list = Free_vars.SS.elements fv.exp_vars in
  let all_params = ref [] in
  let lp_tree = Translate.translate pp_tree in

  Buffer.add_string buf "opaque symbol ";
  Buffer.add_string buf name;
  if prop_list <> [] then begin
    Buffer.add_string buf " (";
    List.iteri (fun i v ->
      if i > 0 then Buffer.add_char buf ' ';
      Pp_lp.pp_ident buf v) prop_list;
    Buffer.add_string buf " : Prop)";
    all_params := prop_list
  end;
  if exp_list <> [] then begin
    Buffer.add_string buf " (";
    List.iteri (fun i v ->
      if i > 0 then Buffer.add_char buf ' ';
      Pp_lp.pp_ident buf v) exp_list;
    Buffer.add_string buf " : \xcf\x84 \xce\xb9)"; (* τ ι *)
    all_params := !all_params @ exp_list
  end;
  Buffer.add_string buf " :\n  \xcf\x80 ("; (* π ( *)
  Pp_lp.pp_prd_block 4 buf goal;
  Buffer.add_string buf ") \xe2\x89\x94\n"; (* ≔ *)
  Buffer.add_string buf "begin\n";
  if !all_params <> [] then begin
    Buffer.add_string buf "  assume ";
    List.iteri (fun i v ->
      if i > 0 then Buffer.add_char buf ' ';
      Pp_lp.pp_ident buf v) !all_params;
    Buffer.add_string buf ";\n"
  end;
  let sink = ref [] in
  Lp_tree.pp ~pad:"  " ~sink buf lp_tree;
  Buffer.add_string buf "\nend;\n";
  (Buffer.contents buf, List.rev !sink)
