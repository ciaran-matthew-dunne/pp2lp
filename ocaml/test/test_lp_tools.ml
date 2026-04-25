(* Lp_tools regression tests — the file scanner has hand-rolled state
   machines for comments / statements / symbol decls / rules. Pin them. *)

open Pp2lp

let failures = ref 0
let total = ref 0
let check label cond =
  incr total;
  if not cond then begin
    incr failures;
    Printf.printf "  FAIL: %s\n" label
  end

(* --- comment stripping --- *)

let test_strip_line_comment () =
  let src = "a // comment\nb" in
  let s = Lp_tools.strip_comments src in
  check "line comment blanked" (s = "a           \nb")

let test_strip_block_comment () =
  let src = "a /* x\ny */ b" in
  let s = Lp_tools.strip_comments src in
  (* /* and */ become spaces, interior is whitespace, newlines preserved *)
  check "block comment preserves newlines"
    (String.contains s '\n');
  check "block comment blanks /* */"
    (not (String.length s >= 4 && String.sub s 2 2 = "/*"))

let test_strip_unterminated_block () =
  let s = Lp_tools.strip_comments "a /* x\ny" in
  check "unterminated /* doesn't crash" (String.length s > 0)

(* --- statement splitter --- *)

let test_split_basic () =
  let stmts = Lp_tools.split_statements "a; b; c;" in
  let bodies = List.map snd stmts in
  check "three statements" (List.length stmts = 3);
  check "bodies in order" (bodies = ["a"; "b"; "c"])

let test_split_respects_parens () =
  let stmts = Lp_tools.split_statements "f(x; y); g;" in
  let bodies = List.map snd stmts in
  check "paren-protected ; doesn't split" (List.length stmts = 2);
  check "first stmt is f(x; y)" (List.nth bodies 0 = "f(x; y)")

let test_split_respects_brackets () =
  let stmts = Lp_tools.split_statements "h[a; b]; i;" in
  check "bracket-protected ; doesn't split" (List.length stmts = 2)

let test_split_lines () =
  let src = "a;\n\nb;\nc;" in
  let stmts = Lp_tools.split_statements src in
  let lines = List.map fst stmts in
  check "line numbers" (lines = [1; 3; 4])

(* --- symbol declaration --- *)

let test_decl_simple () =
  match Lp_tools.parse_symbol_decl "symbol foo : Nat" with
  | Some (n, t, c) ->
    check "name" (n = "foo");
    check "type" (t = "Nat");
    check "not constant" (not c)
  | None -> check "decl parsed" false

let test_decl_constant () =
  match Lp_tools.parse_symbol_decl "constant symbol BTRUE : τ ι" with
  | Some (n, _, c) ->
    check "constant name" (n = "BTRUE");
    check "is constant" c
  | None -> check "constant decl parsed" false

let test_decl_with_modifiers () =
  match Lp_tools.parse_symbol_decl
          "private opaque symbol h_opaque : Prop" with
  | Some (n, _, _) -> check "private opaque name" (n = "h_opaque")
  | None -> check "modifier-prefixed decl parsed" false

let test_decl_with_binders () =
  match Lp_tools.parse_symbol_decl "symbol AR1 [E : τ ι] [R : Prop] : π R" with
  | Some (n, t, _) ->
    check "binder decl name" (n = "AR1");
    check "binder decl type starts at top-level :"
      (* π is the first 2 bytes of the type string *)
      (String.length t >= 2 &&
       Char.code t.[0] = 0xCF && Char.code t.[1] = 0x80)
  | None -> check "binder decl parsed" false

let test_decl_with_definition () =
  (* `≔` = U+2254 = E2 89 94 *)
  let stmt = "symbol foo : Nat \xe2\x89\x94 0" in
  check "definition body detected"
    (Lp_tools.has_definition_body stmt)

let test_decl_no_definition () =
  let stmt = "constant symbol foo : Nat" in
  check "no definition body"
    (not (Lp_tools.has_definition_body stmt))

(* --- propositional check --- *)

let test_propositional () =
  (* π = U+03C0 = CF 80 *)
  check "π Foo is propositional"
    (Lp_tools.is_propositional "\xcf\x80 Foo");
  check "Π … π is propositional"
    (Lp_tools.is_propositional "\xce\xa0 P:Prop, \xcf\x80 P");
  check "τ ι is not propositional"
    (not (Lp_tools.is_propositional "\xcf\x84 \xce\xb9"))

(* --- rewrite rules --- *)

let test_split_with () =
  let parts = Lp_tools.split_on_with_top
                "a ↪ b with c ↪ d with e ↪ f" in
  check "with-split into 3 sub-rules" (List.length parts = 3)

let test_split_with_inside_parens () =
  let parts = Lp_tools.split_on_with_top
                "f (a with b) ↪ g" in
  check "`with` inside parens not split" (List.length parts = 1)

let test_split_arrow () =
  let s = "lhs \xe2\x86\xaa rhs" in (* U+21AA = E2 86 AA *)
  match Lp_tools.split_on_arrow s with
  | Some (l, r) ->
    check "lhs trimmed" (l = "lhs");
    check "rhs trimmed" (r = "rhs")
  | None -> check "arrow split" false

let test_head_of_lhs () =
  check "f x y → f"  (Lp_tools.head_of_lhs "f x y" = "f");
  check "  + a b → +" (Lp_tools.head_of_lhs "  + a b" = "+");
  check "(g h)   → (g" (Lp_tools.head_of_lhs "(g h)" = "")

(* --- requires --- *)

let test_parse_requires_simple () =
  let mods = Lp_tools.parse_requires "require A.B.C" in
  check "module name parsed" (mods = ["A.B.C"])

let test_parse_requires_open () =
  let mods = Lp_tools.parse_requires "require open pp2lp.B pp2lp.Rules" in
  check "two open requires"
    (mods = ["pp2lp.B"; "pp2lp.Rules"])

let test_parse_requires_not_a_require () =
  let mods = Lp_tools.parse_requires "symbol foo : Nat" in
  check "non-require returns []" (mods = [])

(* --- end-to-end on a synthetic file --- *)

let with_tmp_file s f =
  let p = Filename.temp_file "lp_tools_test_" ".lp" in
  let oc = open_out p in
  output_string oc s; close_out oc;
  Fun.protect ~finally:(fun () -> try Unix.unlink p with _ -> ()) (fun () -> f p)

let test_scan_file_admits () =
  with_tmp_file
    "// header\nsymbol foo : Nat \xe2\x89\x94\nbegin admit end;\n\
     opaque symbol bar : Prop \xe2\x89\x94 begin\n  admit\nend;"
    (fun p ->
      let _, _, admits = Lp_tools.scan_file p in
      check "two admits found" (List.length admits = 2))

let test_scan_file_assumption () =
  with_tmp_file
    "constant symbol foo : Nat;\n\
     symbol bar : Prop \xe2\x89\x94 my_proof;"
    (fun p ->
      let assums, _, _ = Lp_tools.scan_file p in
      check "one assumption (foo, not bar)"
        (List.length assums = 1);
      match assums with
      | [a] ->
        check "assumption name" (a.Lp_tools.name = "foo");
        check "assumption is constant" a.constant
      | _ -> check "exactly one assumption" false)

let test_scan_file_rules () =
  with_tmp_file "rule + 0 x \xe2\x86\xaa x;" (fun p ->
    let _, rules, _ = Lp_tools.scan_file p in
    check "one rewrite rule" (List.length rules = 1);
    match rules with
    | [r] ->
      check "rule head is +" (r.Lp_tools.symbol = "+");
      check "lhs normalised" (r.lhs = "+ 0 x")
    | _ -> check "exactly one rule" false)

(* --- probe insertion --- *)

let test_apply_insertions_basic () =
  let lines = ["a"; "b"; "c"] in
  let new_lines, mapping =
    Lp_tools.apply_insertions lines [(2, "X")]
  in
  check "insertion before line 2" (new_lines = ["a"; "X"; "b"; "c"]);
  check "mapping reports probe line 2" (mapping = [(2, "X")])

let test_apply_insertions_at_start () =
  let lines = ["a"; "b"] in
  let new_lines, _ = Lp_tools.apply_insertions lines [(1, "X")] in
  check "insertion at line 1" (new_lines = ["X"; "a"; "b"])

let test_apply_insertions_past_eof () =
  let lines = ["a"; "b"] in
  let new_lines, mapping =
    Lp_tools.apply_insertions lines [(99, "X")] in
  check "insertion past EOF appended" (new_lines = ["a"; "b"; "X"]);
  check "mapping past EOF" (mapping = [(3, "X")])

let test_apply_insertions_two_at_different_lines () =
  let lines = ["a"; "b"; "c"; "d"] in
  let new_lines, mapping =
    Lp_tools.apply_insertions lines [(2, "X"); (4, "Y")] in
  check "two insertions" (new_lines = ["a"; "X"; "b"; "c"; "Y"; "d"]);
  check "mapping for two insertions"
    (mapping = [(2, "X"); (5, "Y")])

let test_apply_insertions_two_at_same_line () =
  let lines = ["a"; "b"] in
  let new_lines, _ =
    Lp_tools.apply_insertions lines [(2, "X"); (2, "Y")] in
  check "two at same line preserved in order"
    (new_lines = ["a"; "X"; "Y"; "b"])

(* --- ANSI strip --- *)

let test_strip_ansi_local_basic () =
  let s = "\x1b[36m[unif]\x1b[0m solve foo" in
  check "ANSI stripped"
    (Lp_tools.strip_ansi_local s = "[unif] solve foo")

(* --- session marker slicing --- *)

let test_between_session_markers () =
  let raw = "Start checking \"foo.lp\"\nbody\nEnd checking \"foo.lp\"\n" in
  let body = Lp_tools.between_session_markers raw in
  check "session body extracted" (body = "body")

let test_between_session_markers_no_markers () =
  let raw = "no markers here\n" in
  let body = Lp_tools.between_session_markers raw in
  check "no markers → original returned" (body = "no markers here")

(* --- echo slicing (lp-debug uses this on stderr) --- *)

let test_slice_between_echoes_basic () =
  let raw = "ignored\ndebug +u\nevent1\nevent2\ndebug -u\nignored\n" in
  let body = Lp_tools.slice_between_echoes raw
               ~start_echo:"debug +u" ~end_echo:"debug -u" in
  check "between echoes" (body = "event1\nevent2")

let test_slice_between_echoes_missing_start () =
  let raw = "ignored\nevent1\ndebug -u\nignored\n" in
  let body = Lp_tools.slice_between_echoes raw
               ~start_echo:"debug +u" ~end_echo:"debug -u" in
  check "missing start_echo → empty" (body = "")

let () =
  test_strip_line_comment ();
  test_strip_block_comment ();
  test_strip_unterminated_block ();
  test_split_basic ();
  test_split_respects_parens ();
  test_split_respects_brackets ();
  test_split_lines ();
  test_decl_simple ();
  test_decl_constant ();
  test_decl_with_modifiers ();
  test_decl_with_binders ();
  test_decl_with_definition ();
  test_decl_no_definition ();
  test_propositional ();
  test_split_with ();
  test_split_with_inside_parens ();
  test_split_arrow ();
  test_head_of_lhs ();
  test_parse_requires_simple ();
  test_parse_requires_open ();
  test_parse_requires_not_a_require ();
  test_scan_file_admits ();
  test_scan_file_assumption ();
  test_scan_file_rules ();
  test_apply_insertions_basic ();
  test_apply_insertions_at_start ();
  test_apply_insertions_past_eof ();
  test_apply_insertions_two_at_different_lines ();
  test_apply_insertions_two_at_same_line ();
  test_strip_ansi_local_basic ();
  test_between_session_markers ();
  test_between_session_markers_no_markers ();
  test_slice_between_echoes_basic ();
  test_slice_between_echoes_missing_start ();
  Printf.printf "%d/%d lp_tools tests passed\n"
    (!total - !failures) !total;
  if !failures > 0 then exit 1
