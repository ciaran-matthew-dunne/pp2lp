(* Minimal pp2lp CLI: read one .trace file and emit Lambdapi to stdout. *)

let die fmt =
  Printf.ksprintf (fun s -> prerr_string s; prerr_newline (); exit 1) fmt

let emit_trace fp =
  try
    let proof = Pp2lp.Reconstruct.reconstruct_symbol fp in
    print_string Pp2lp.Emit_lp.lp_header;
    print_char '\n';
    print_string proof;
    print_char '\n'
  with
  | Pp2lp.Parse_trace.Bad_trace m ->
    die "parse error in %s: %s" fp m
  | Pp2lp.Proof_tree.Bad_trace m ->
    die "tree-build error in %s: %s" fp m
  | exn ->
    die "ERROR %s: %s" fp (Printexc.to_string exn)

let usage () =
  prerr_endline "Usage: pp2lp TRACE";
  prerr_endline "Emit Lambdapi for one PP .trace file to stdout."

let () =
  match Array.to_list Sys.argv with
  | [_; ("--help" | "-help" | "-h")] -> usage ()
  | [_; fp] -> emit_trace fp
  | [_; "--"; fp] -> emit_trace fp
  | _ -> usage (); exit 1
