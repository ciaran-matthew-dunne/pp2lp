open Pp2lp.Syntax_pp
open Pp2lp.Parse_pp
open Pp2lp.Proof_tree
open Pp2lp.Emit_lp
open Pp2lp.Emit_pp
open Pp2lp.Reconstruct



let tests_passed = ref 0
let tests_failed = ref 0

let check name cond =
  if cond then
    incr tests_passed
  else begin
    Printf.printf "FAIL: %s\n" name;
    incr tests_failed
  end

let parse_exn s =
  match parse_pp_string s with
  | Some line -> line
  | None -> failwith (Printf.sprintf "Failed to parse: %s" s)

(* Helper: check if substring is present in output *)
let has s output =
  try ignore (Str.search_forward (Str.regexp_string s) output 0); true
  with Not_found -> false

(* ===================================================================
   SECTION 1: Parser unit tests
   =================================================================== *)

(* --- Simple rules --- *)

let () =
  let (lhs, rhs) = parse_exn "[AND1] <p and q>" in
  check "parse: AND1 lhs" (lhs = ("AND1", None));
  check "parse: AND1 rhs"
    (rhs = Simple (Binary (And, Lift (Var "p"), Lift (Var "q"))))

let () =
  let (lhs, rhs) = parse_exn "[AXM1] <VRAI>" in
  check "parse: AXM1 lhs" (lhs = ("AXM1", None));
  check "parse: AXM1 rhs" (rhs = Simple (Lift (Var "VRAI")))

(* --- Connectives --- *)

let () =
  let (_, rhs) = parse_exn "[IMP4] <p => q>" in
  check "parse: implication" (rhs = Simple (Binary (Imp, Lift (Var "p"), Lift (Var "q"))))

let () =
  let (_, rhs) = parse_exn "[OR1] <p or q>" in
  check "parse: disjunction" (rhs = Simple (Binary (Or, Lift (Var "p"), Lift (Var "q"))))

let () =
  let (_, rhs) = parse_exn "[NOT1] <not(p)>" in
  check "parse: negation" (rhs = Simple (Unary (Not, Lift (Var "p"))))

let () =
  let (_, rhs) = parse_exn "[EQ1] <p <=> q>" in
  check "parse: iff" (rhs = Simple (Binary (Iff, Lift (Var "p"), Lift (Var "q"))))

(* --- Equality and comparison --- *)

let () =
  let (_, rhs) = parse_exn "[EQ1] <a = b>" in
  check "parse: equality" (rhs = Simple (Eq (Var "a", Var "b")))

let () =
  let (_, rhs) = parse_exn "[AR1] <a <= b>" in
  check "parse: leq" (rhs = Simple (Leq (Var "a", Var "b")))

(* --- Arithmetic --- *)

let () =
  let (_, rhs) = parse_exn "[AR1] <a + b = c>" in
  check "parse: addition in equality"
    (rhs = Simple (Eq (AOp (Add, Var "a", Var "b"), Var "c")))

let () =
  let (_, rhs) = parse_exn "[AR1] <a - b <= 0>" in
  check "parse: subtraction in leq"
    (rhs = Simple (Leq (AOp (Sub, Var "a", Var "b"), Nat 0)))

let () =
  let (_, rhs) = parse_exn "[AR1] <-a <= 0>" in
  check "parse: unary minus"
    (rhs = Simple (Leq (Neg (Var "a"), Nat 0)))

(* --- Membership --- *)

let () =
  let (_, rhs) = parse_exn "[STOP] <x: S>" in
  check "parse: single membership" (rhs = Simple (Mem ([Var "x"], Var "S")))

let () =
  let (_, rhs) = parse_exn "[STOP] <x, y: S>" in
  check "parse: multi membership" (rhs = Simple (Mem ([Var "x"; Var "y"], Var "S")))

(* --- Quantifiers --- *)

let () =
  let (_, rhs) = parse_exn "[ALL1] <!x.p>" in
  check "parse: forall0" (rhs = Simple (Bind (Bang, ["x"], Lift (Var "p"))))

let () =
  let (_, rhs) = parse_exn "[ALL1] <forall(x,y).p>" in
  check "parse: forall1 multi" (rhs = Simple (Bind (Forall, ["x"; "y"], Lift (Var "p"))))

let () =
  let (_, rhs) = parse_exn "[ALL1] <#x.p>" in
  check "parse: exists" (rhs = Simple (Bind (Exists, ["x"], Lift (Var "p"))))

(* --- Function application --- *)

let () =
  let (_, rhs) = parse_exn "[AXM1] <p(a, b)>" in
  check "parse: function app"
    (rhs = Simple (Lift (App ("p", [Var "a"; Var "b"]))))

(* --- LHS with arguments --- *)

let () =
  let (lhs, _) = parse_exn "[ALL8(1)] <VRAI>" in
  check "parse: lhs int arg" (lhs = ("ALL8", Some (Pred (Lift (Nat 1)))))

let () =
  let (lhs, _) = parse_exn "[AR3(-a | 1+a)] <VRAI>" in
  check "parse: lhs pipe arg"
    (lhs = ("AR3", Some (PipeArg (Neg (Var "a"), AOp (Add, Nat 1, Var "a")))))

let () =
  let (lhs, _) = parse_exn "[AR10(x: S)] <VRAI>" in
  check "parse: lhs membership arg"
    (lhs = ("AR10", Some (Pred (Mem ([Var "x"], Var "S")))))

let () =
  let (lhs, _) = parse_exn "[AR9(-e)] <VRAI>" in
  check "parse: lhs expression arg"
    (lhs = ("AR9", Some (Pred (Lift (Neg (Var "e"))))))

(* --- FIN lines --- *)

let () =
  let (lhs, rhs) = parse_exn
    "[FIN(VRAI)] <FIN(VRAI | (Hyp |- p) | (Hyp |- q) | 3)>"
  in
  check "parse: FIN lhs" (lhs = ("FIN", Some (Pred (Lift (Var "VRAI")))));
  check "parse: FIN rhs"
    (rhs = Fin (Lift (Var "VRAI"),
                ([], Lift (Var "p")),
                ([], Lift (Var "q")),
                3))

let () =
  let (_, rhs) = parse_exn
    "[FIN(VRAI)] <FIN(VRAI | (Hyp,p(a,b) |- q) | (Hyp |- r) | 5)>"
  in
  check "parse: FIN with hyp"
    (rhs = Fin (Lift (Var "VRAI"),
                ([Lift (App ("p", [Var "a"; Var "b"]))], Lift (Var "q")),
                ([], Lift (Var "r")),
                5))

let () =
  let (_, rhs) = parse_exn
    "[FIN(VRAI)] <FIN(VRAI | (Hyp,!x.not(p) |- q) | (Hyp |- r) | 7)>"
  in
  check "parse: FIN with binding hyp"
    (rhs = Fin (Lift (Var "VRAI"),
                ([Bind (Bang, ["x"], Unary (Not, Lift (Var "p")))],
                 Lift (Var "q")),
                ([], Lift (Var "r")),
                7))

let () =
  let (_, rhs) = parse_exn
    "[FIN(VRAI)] <FIN(VRAI | (Hyp,a-b<=0 |- q) | (Hyp |- r) | 1)>"
  in
  check "parse: hyp with leq"
    (rhs = Fin (Lift (Var "VRAI"),
                ([Leq (AOp (Sub, Var "a", Var "b"), Nat 0)],
                 Lift (Var "q")),
                ([], Lift (Var "r")),
                1))

let () =
  let (_, rhs) = parse_exn
    "[FIN(VRAI)] <FIN(VRAI | (Hyp,(x,y: S) |- q) | (Hyp |- r) | 1)>"
  in
  check "parse: hyp with paren membership"
    (rhs = Fin (Lift (Var "VRAI"),
                ([Mem ([Var "x"; Var "y"], Var "S")],
                 Lift (Var "q")),
                ([], Lift (Var "r")),
                1))

(* --- Set operators --- *)

let () =
  let (_, rhs) = parse_exn "[STOP] <x: FIN(S)>" in
  check "parse: FIN as set constructor"
    (rhs = Simple (Mem ([Var "x"], App ("FIN", [Var "S"]))))

let () =
  let (_, rhs) = parse_exn "[STOP] <a /\\ b = c>" in
  check "parse: intersection"
    (rhs = Simple (Eq (Inter (Var "a", Var "b"), Var "c")))

let () =
  let (_, rhs) = parse_exn "[STOP] <a \\/ b = c>" in
  check "parse: union"
    (rhs = Simple (Eq (Union (Var "a", Var "b"), Var "c")))

(* --- Precedence --- *)

let () =
  let (_, rhs) = parse_exn "[AR1] <a - b - c <= 0>" in
  check "parse: left assoc subtraction"
    (rhs = Simple (Leq (AOp (Sub, AOp (Sub, Var "a", Var "b"), Var "c"), Nat 0)))

let () =
  let (_, rhs) = parse_exn "[AND1] <p and q => r>" in
  check "parse: and/imp precedence"
    (rhs = Simple (Binary (Imp, Binary (And, Lift (Var "p"), Lift (Var "q")),
                           Lift (Var "r"))))

let () =
  let (_, rhs) = parse_exn "[AR1] <e-f-x<=0 and -f+x-g<=0 => x: h>" in
  check "parse: complex arith predicate"
    (match rhs with Simple (Binary (Imp, Binary (And, Leq _, Leq _), Mem _)) -> true
                  | _ -> false)

(* PP spec: <=> (priority 1) binds tighter than and/or (priority 2) *)
let () =
  let (_, rhs) = parse_exn "[EQV3] <p <=> q and r>" in
  check "parse: iff/and precedence"
    (rhs = Simple (Binary (And, Binary (Iff, Lift (Var "p"), Lift (Var "q")),
                           Lift (Var "r"))))

let () =
  let (_, rhs) = parse_exn "[EQV3] <p <=> q or r>" in
  check "parse: iff/or precedence"
    (rhs = Simple (Binary (Or, Binary (Iff, Lift (Var "p"), Lift (Var "q")),
                           Lift (Var "r"))))

(* --- Multiple hypotheses --- *)

let () =
  let (_, rhs) = parse_exn
    "[FIN(VRAI)] <FIN(VRAI | (Hyp,not(a = b),not(c = d) |- q) | (Hyp |- r) | 1)>"
  in
  check "parse: multiple hyps"
    (match rhs with
     | Fin (_, (hyps, _), _, _) -> List.length hyps = 2
     | _ -> false)

(* --- Parse failure returns None --- *)

let () =
  check "parse: bad input returns None" (parse_pp_string "garbage @@@ $$$" = None)


(* ===================================================================
   SECTION 2: Emit_lp pretty-printer unit tests
   =================================================================== *)

(* --- Expression printing --- *)

let () =
  check "emit: var" (exp_to_string (Var "x") = "x")

let () =
  check "emit: VRAI" (exp_to_string (Var "VRAI") = "BTRUE")

let () =
  check "emit: FAUX" (exp_to_string (Var "FAUX") = "BFALSE")

let () =
  check "emit: nat 0" (exp_to_string (Nat 0) = "\xf0\x9d\x9f\x8e")

let () =
  check "emit: nat 1" (exp_to_string (Nat 1) = "\xf0\x9d\x9f\x8f")

let () =
  check "emit: add"
    (exp_to_string (AOp (Add, Var "a", Var "b")) = "(a + b)")

let () =
  check "emit: sub"
    (exp_to_string (AOp (Sub, Var "a", Var "b")) = "(a - b)")

let () =
  check "emit: neg"
    (has "\xe2\x80\x94" (exp_to_string (Neg (Var "x"))))  (* — *)

let () =
  check "emit: app"
    (exp_to_string (App ("f", [Var "a"; Var "b"])) =
     "(eapp f (a \xe2\x86\xa6 b))")

let () =
  check "emit: app single"
    (exp_to_string (App ("f", [Var "a"])) =
     "(eapp f a)")

(* --- Predicate printing (shallow encoding) --- *)

let () =
  check "emit: lift var"
    (prd_to_string (Lift (Var "p")) = "p")

let () =
  check "emit: lift VRAI"
    (prd_to_string (Lift (Var "VRAI")) = "\xe2\x8a\xa4") (* ⊤ *)

let () =
  check "emit: lift FAUX"
    (prd_to_string (Lift (Var "FAUX")) = "\xe2\x8a\xa5") (* ⊥ *)

let () =
  check "emit: not"
    (prd_to_string (Unary (Not, Lift (Var "p"))) =
     "(\xc2\xac p)")

let () =
  check "emit: and"
    (prd_to_string (Binary (And, Lift (Var "p"), Lift (Var "q"))) =
     "(p \xe2\x88\xa7 q)")

let () =
  check "emit: or"
    (prd_to_string (Binary (Or, Lift (Var "p"), Lift (Var "q"))) =
     "(p \xe2\x88\xa8 q)")

let () =
  check "emit: imp"
    (prd_to_string (Binary (Imp, Lift (Var "p"), Lift (Var "q"))) =
     "(p \xe2\x87\x92 q)")

let () =
  check "emit: iff"
    (prd_to_string (Binary (Iff, Lift (Var "p"), Lift (Var "q"))) =
     "(p \xe2\x87\x94 q)")

let () =
  check "emit: eq"
    (prd_to_string (Eq (Var "a", Var "b")) =
     "(a = b)")

let () =
  check "emit: leq"
    (prd_to_string (Leq (Var "a", Var "b")) =
     "(a \xe2\x89\xa4 b)")

let () =
  check "emit: mem"
    (prd_to_string (Mem ([Var "x"], Var "S")) =
     "(x \xcf\xb5 S)")  (* ϵ *)

let () =
  check "emit: papp"
    (prd_to_string (Lift (App ("f", [Var "a"; Var "b"]))) =
     "((a \xe2\x86\xa6 b) \xcf\xb5 f)")

let () =
  check "emit: forall0 HOAS"
    (has "`\xe2\x88\x80"
      (prd_to_string (Bind (Bang, ["x"], Eq (Var "x", Var "x")))))

let () =
  check "emit: nested connectives"
    (prd_to_string
       (Binary (Imp,
                Unary (Not, Binary (And, Lift (Var "p"), Lift (Var "q"))),
                Binary (Or, Unary (Not, Lift (Var "p")),
                            Unary (Not, Lift (Var "q"))))) =
     "(\xc2\xac (p \xe2\x88\xa7 q) \xe2\x87\x92 \xc2\xac p \xe2\x88\xa8 \xc2\xac q)")


(* ===================================================================
   SECTION 3: Proof tree building tests
   =================================================================== *)

(* Helper: parse replay string into lines *)
let parse_replay_string s =
  let lines = String.split_on_char '\n' s in
  List.filter_map (fun line ->
    let trimmed = String.trim line in
    if trimmed = "" then None
    else parse_pp_string trimmed
  ) lines

(* --- Leaf rule --- *)
let () =
  let lines = parse_replay_string "[AXM1] <VRAI>" in
  let tree = build lines in
  match tree with
  | Apply { rule = "AXM1"; children = []; _ } ->
    check "tree: leaf AXM1" true
  | _ -> check "tree: leaf AXM1" false

(* --- Single child (1-arity) --- *)
let () =
  let lines = parse_replay_string
    "[OR1] <not(p or q) => not(p)>\n\
     [IMP4] <not(p) => (not(q) => not(p))>\n\
     [AXM4] <not(q) => not(p)>"
  in
  let tree = build lines in
  match tree with
  | Apply { rule = "OR1"; children = [
      Apply { rule = "IMP4"; children = [
        Apply { rule = "AXM4"; children = []; _ }
      ]; _ }
    ]; _ } ->
    check "tree: chain OR1→IMP4→AXM4" true
  | _ -> check "tree: chain OR1→IMP4→AXM4" false

(* --- Two children (2-arity branching) --- *)
let () =
  let lines = parse_replay_string
    "[AND4] <q and p>\n\
     [AXM3] <p>\n\
     [AXM3] <q>"
  in
  let tree = build lines in
  match tree with
  | Apply { rule = "AND4"; children = [
      Apply { rule = "AXM3"; children = []; _ };
      Apply { rule = "AXM3"; children = []; _ }
    ]; _ } ->
    check "tree: branch AND4→(AXM3, AXM3)" true
  | _ -> check "tree: branch AND4→(AXM3, AXM3)" false

(* --- Full trace 03: mixed chain + branch --- *)
let () =
  let lines = parse_replay_string
    "[AND3] <p and q => q and p>\n\
     [IMP4] <p => (q => q and p)>\n\
     [AR10(q)] <q => q and p>\n\
     [IMP4] <q => q and p>\n\
     [AND4] <q and p>\n\
     [AXM3] <p>\n\
     [AXM3] <q>"
  in
  let tree = build lines in
  match tree with
  | Apply { rule = "AND3"; children = [
      Apply { rule = "IMP4"; children = [
        Apply { rule = "IMP4"; children = [
          Apply { rule = "AND4"; children = [
            Apply { rule = "AXM3"; _ };
            Apply { rule = "AXM3"; _ }
          ]; _ }
        ]; _ }
      ]; _ }
    ]; _ } ->
    check "tree: trace 03 structure" true
  | _ -> check "tree: trace 03 structure" false

(* --- Skip lines: AR10 is skipped (-1 arity) --- *)
let () =
  let lines = parse_replay_string
    "[AR10(q)] <q => q and p>\n\
     [AXM1] <VRAI>"
  in
  let tree = build lines in
  match tree with
  | Apply { rule = "AXM1"; children = []; _ } ->
    check "tree: AR10 skipped" true
  | _ -> check "tree: AR10 skipped" false

(* --- Full trace 01: branching with AND1 --- *)
let () =
  let lines = parse_replay_string
    "[AND1] <not(p and q) => not(p) or not(q)>\n\
     [IMP4] <not(q) => not(p) or not(q)>\n\
     [OR4] <not(p) or not(q)>\n\
     [AXM4] <not(not(p)) => not(q)>\n\
     [IMP4] <not(p) => not(p) or not(q)>\n\
     [OR4] <not(p) or not(q)>\n\
     [NOT1] <not(not(p)) => not(q)>\n\
     [AXM1] <p => not(q)>"
  in
  let tree = build lines in
  match tree with
  | Apply { rule = "AND1"; children = [child1; child2]; _ } ->
    let ok1 = match child1 with
      | Apply { rule = "IMP4"; children = [
          Apply { rule = "OR4"; children = [
            Apply { rule = "AXM4"; children = []; _ }
          ]; _ }
        ]; _ } -> true
      | _ -> false
    in
    let ok2 = match child2 with
      | Apply { rule = "IMP4"; children = [
          Apply { rule = "OR4"; children = [
            Apply { rule = "NOT1"; children = [
              Apply { rule = "AXM1"; children = []; _ }
            ]; _ }
          ]; _ }
        ]; _ } -> true
      | _ -> false
    in
    check "tree: trace 01 left branch" ok1;
    check "tree: trace 01 right branch" ok2
  | _ ->
    check "tree: trace 01 left branch" false;
    check "tree: trace 01 right branch" false

(* --- Primed context: STOP_1 --- *)
let () =
  let lines = parse_replay_string "[STOP_1] <FAUX>" in
  let tree = build lines in
  match tree with
  | Apply { rule = "STOP_1"; ctx = Primed; children = []; _ } ->
    check "tree: STOP_1 primed" true
  | _ -> check "tree: STOP_1 primed" false

(* --- Rule arity table --- *)
let () =
  check "arity: AXM1 = 0" (rule_arity "AXM1" = 0);
  check "arity: AXM9 = 0" (rule_arity "AXM9" = 0);
  check "arity: VR1 = 0" (rule_arity "VR1" = 0);
  check "arity: FX3 = 0" (rule_arity "FX3" = 0);
  check "arity: AND1 = 2" (rule_arity "AND1" = 2);
  check "arity: OR2 = 2" (rule_arity "OR2" = 2);
  check "arity: ALL7 = 2" (rule_arity "ALL7" = 2);
  check "arity: XST8 = 2" (rule_arity "XST8" = 2);
  check "arity: AND2 = 1" (rule_arity "AND2" = 1);
  check "arity: IMP4 = 1" (rule_arity "IMP4" = 1);
  check "arity: FIN = -1" (rule_arity "FIN" = -1);
  check "arity: STOP_NORM = -1" (rule_arity "STOP_NORM" = -1);
  check "arity: NRM = -1" (rule_arity "NRM" = -1);
  check "arity: AR10 = -1" (rule_arity "AR10" = -1)

(* --- has_primed --- *)
let () =
  check "primed: AND1 yes" (has_primed "AND1" = true);
  check "primed: STOP yes" (has_primed "STOP" = true);
  check "primed: AXM9 yes" (has_primed "AXM9" = true);
  check "primed: FIN no" (has_primed "FIN" = false)

(* --- resolve_rule --- *)
let () =
  check "resolve: AND1 Base" (resolve_rule "AND1" Base = "AND1");
  check "resolve: AND1 Primed" (resolve_rule "AND1" Primed = "AND1_1");
  check "resolve: FIN Base" (resolve_rule "FIN" Base = "FIN");
  check "resolve: FIN Primed" (resolve_rule "FIN" Primed = "FIN")


(* ===================================================================
   SECTION 4: Reconstruct module tests
   =================================================================== *)

(* --- goal_of_tree --- *)
let () =
  let lines = parse_replay_string
    "[AND1] <p and q>\n\
     [AXM3] <p>"
  in
  let tree = build lines in
  let goal = goal_of_tree tree in
  check "reconstruct: goal_of_tree"
    (goal = Binary (And, Lift (Var "p"), Lift (Var "q")))

(* --- name_of_file --- *)
let () =
  check "reconstruct: name_of_file .replay"
    (name_of_file "foo/03.trace.replay" = "{|03.trace|}");
  check "reconstruct: name_of_file .replay only"
    (name_of_file "bar/test.replay" = "{|test|}");
  check "reconstruct: name_of_file plain"
    (name_of_file "baz/hello" = "{|hello|}")

(* --- reconstruct_lines produces valid output --- *)
let () =
  let lines = parse_replay_string
    "[AND3] <p and q => q and p>\n\
     [IMP4] <p => (q => q and p)>\n\
     [AR10(q)] <q => q and p>\n\
     [IMP4] <q => q and p>\n\
     [AND4] <q and p>\n\
     [AXM3] <p>\n\
     [AXM3] <q>"
  in
  let output = reconstruct_lines "test03" lines in
  (* Check that the output contains key structural elements *)
  check "reconstruct: has require" (has "require open" output);
  check "reconstruct: has symbol" (has "symbol test03" output);
  check "reconstruct: has begin/end" (has "begin" output && has "end;" output);
  check "reconstruct: has refine AND3" (has "refine AND3" output);
  check "reconstruct: has refine AND4" (has "refine AND4" output);
  check "reconstruct: has goal predicate" (has "\xe2\x87\x92" output) (* ⇒ *)

(* --- reconstruct_lines for branching trace --- *)
let () =
  let lines = parse_replay_string
    "[AND1] <not(p and q) => not(p) or not(q)>\n\
     [IMP4] <not(q) => not(p) or not(q)>\n\
     [OR4] <not(p) or not(q)>\n\
     [AXM4] <not(not(p)) => not(q)>\n\
     [IMP4] <not(p) => not(p) or not(q)>\n\
     [OR4] <not(p) or not(q)>\n\
     [NOT1] <not(not(p)) => not(q)>\n\
     [AXM1] <p => not(q)>"
  in
  let output = reconstruct_lines "test01" lines in
  (* Branching output should have { } blocks *)
  check "reconstruct: branching has braces" (has "{ " output);
  check "reconstruct: branching has close brace" (has "}" output)


(* ===================================================================
   SECTION 4b: Hypothesis extraction and pattern matching tests
   =================================================================== *)

(* --- collect_conj_hyps --- *)
let () =
  let p = Lift (Var "p") in
  let q = Lift (Var "q") in
  let r = Lift (Var "r") in
  (* Single predicate *)
  check "collect_conj_hyps: single" (collect_conj_hyps [] p = [p]);
  (* p ∧ q → [q; p] (reverse order due to acc) *)
  let conj = Binary (And, p, q) in
  let result = collect_conj_hyps [] conj in
  check "collect_conj_hyps: two" (List.length result = 2);
  (* p ∧ q ∧ r → three elements *)
  let conj3 = Binary (And, Binary (And, p, q), r) in
  let result3 = collect_conj_hyps [] conj3 in
  check "collect_conj_hyps: three" (List.length result3 = 3)

(* --- extract_theorem_hyps --- *)
let () =
  let p = Lift (Var "p") in
  let q = Lift (Var "q") in
  let r = Lift (Var "r") in
  (* No hyps: plain predicate *)
  check "extract_hyps: no hyps" (extract_theorem_hyps p = []);
  (* ∀ x (p ∧ q ⇒ r) → [q; p] *)
  let thm = Bind (Bang, ["x"],
    Binary (Imp, Binary (And, p, q), r)) in
  let hyps = extract_theorem_hyps thm in
  check "extract_hyps: forall imp" (List.length hyps = 2);
  (* p ∧ q ∧ r ⇒ p → three hyps *)
  let thm2 = Binary (Imp, Binary (And, Binary (And, p, q), r), p) in
  let hyps2 = extract_theorem_hyps thm2 in
  check "extract_hyps: nested conj" (List.length hyps2 = 3);
  (* Nested ∀ stripping *)
  let thm3 = Bind (Bang, ["x"], Bind (Bang, ["y"],
    Binary (Imp, p, q))) in
  let hyps3 = extract_theorem_hyps thm3 in
  check "extract_hyps: nested forall" (List.length hyps3 = 1)

(* --- emit_lp structure for leaf rule --- *)
let () =
  let lines = parse_replay_string "[AXM1] <VRAI>" in
  let tree = build lines in
  let goal = goal_of_tree tree in
  let output = emit_lp "test_leaf" goal tree in
  check "emit_lp: leaf has require" (has "require open" output);
  check "emit_lp: leaf has pi" (has "\xcf\x80" output);
  check "emit_lp: leaf has refine AXM1" (has "refine AXM1" output)

(* --- emit_lp for sequential chain --- *)
let () =
  let lines = parse_replay_string
    "[IMP4] <p => q>\n\
     [AXM3] <q>"
  in
  let tree = build lines in
  let goal = goal_of_tree tree in
  let output = emit_lp "test_seq" goal tree in
  check "emit_lp: seq has semicolon" (has ";" output);
  check "emit_lp: seq has IMP4" (has "refine IMP4" output);
  check "emit_lp: seq has AXM3" (has "refine AXM3" output)

(* --- emit_lp for branching --- *)
let () =
  let lines = parse_replay_string
    "[AND1] <p and q>\n\
     [AXM3] <p>\n\
     [AXM3] <q>"
  in
  let tree = build lines in
  let goal = goal_of_tree tree in
  let output = emit_lp "test_branch" goal tree in
  check "emit_lp: branch has braces" (has "{ " output && has "}" output);
  check "emit_lp: branch has AND1" (has "refine AND1" output)


(* ===================================================================
   SECTION 5: Emit_pp round-trip tests (parse → emit_pp → re-parse)
   =================================================================== *)

(* Round-trip helper: wrap predicate text in a STOP line, parse, emit, re-parse *)
let roundtrip_prd text =
  let line = Printf.sprintf "[STOP] <%s>" text in
  match parse_pp_string line with
  | None -> failwith (Printf.sprintf "roundtrip: initial parse failed: %s" text)
  | Some (_, Simple p) ->
    let emitted = prd_to_pp p in
    let line2 = Printf.sprintf "[STOP] <%s>" emitted in
    (match parse_pp_string line2 with
     | None -> failwith (Printf.sprintf "roundtrip: re-parse failed: %s" emitted)
     | Some (_, Simple p2) -> (p, emitted, p2)
     | _ -> failwith "roundtrip: unexpected FIN on re-parse")
  | _ -> failwith "roundtrip: unexpected FIN"

let check_roundtrip name text =
  let (p, _emitted, p2) = roundtrip_prd text in
  check name (p = p2)

(* --- Simple predicates --- *)
let () = check_roundtrip "rt: var" "p"
let () = check_roundtrip "rt: btrue" "btrue"
let () = check_roundtrip "rt: bfalse" "bfalse"
let () = check_roundtrip "rt: not" "not(p)"
let () = check_roundtrip "rt: and" "(p and q)"
let () = check_roundtrip "rt: or" "(p or q)"
let () = check_roundtrip "rt: imp" "(p => q)"
let () = check_roundtrip "rt: iff" "(p <=> q)"

(* --- Equality and comparison --- *)
let () = check_roundtrip "rt: eq" "a=b"
let () = check_roundtrip "rt: leq" "a<=b"

(* --- Membership --- *)
let () = check_roundtrip "rt: mem" "x:S"
let () = check_roundtrip "rt: multi mem" "x,y:S"

(* --- Quantifiers --- *)
let () = check_roundtrip "rt: forall0" "!x.(p)"
let () = check_roundtrip "rt: forall1" "forall(x,y).(p)"
let () = check_roundtrip "rt: exists" "#x.(p)"

(* --- Arithmetic --- *)
let () = check_roundtrip "rt: add" "a+b=c"
let () = check_roundtrip "rt: sub" "a-b<=0"
let () = check_roundtrip "rt: neg" "-a<=0"

(* --- Set operators --- *)
let () = check_roundtrip "rt: inter" "a/\\b=c"
let () = check_roundtrip "rt: union" "a\\/b=c"
let () = check_roundtrip "rt: set image" "a[b]=c"

(* --- Nested --- *)
let () = check_roundtrip "rt: nested" "(not(p and q) => (not(p) or not(q)))"
let () = check_roundtrip "rt: forall imp" "!x.((p and q) => r)"
let () = check_roundtrip "rt: app mem" "a,b:f"

(* --- exp_to_pp direct tests --- *)
let () =
  check "emit_pp: var" (exp_to_pp (Var "x") = "x");
  check "emit_pp: nat" (exp_to_pp (Nat 42) = "42");
  check "emit_pp: add" (exp_to_pp (AOp (Add, Var "a", Var "b")) = "a+b");
  check "emit_pp: sub" (exp_to_pp (AOp (Sub, Var "a", Var "b")) = "a-b");
  check "emit_pp: neg" (exp_to_pp (Neg (Var "x")) = "-x");
  check "emit_pp: app" (exp_to_pp (App ("f", [Var "a"; Var "b"])) = "f(a,b)");
  check "emit_pp: inter" (exp_to_pp (Inter (Var "a", Var "b")) = "a/\\b");
  check "emit_pp: union" (exp_to_pp (Union (Var "a", Var "b")) = "a\\/b");
  check "emit_pp: image" (exp_to_pp (SetImage (Var "a", Var "b")) = "a[b]")


(* --- Summary --- *)

let () =
  Printf.printf "%d passed, %d failed\n" !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
