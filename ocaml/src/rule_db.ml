(* Rule database: static metadata for PP inference rules. *)

type rule_info = {
  arity: int;           (* -1=phantom, 0=leaf, 1=single child, 2=two children *)
  emit_args: string option;
  result_schema: int;   (* 0=leaf/TRUE, 1=passthrough, 2=conjunction *)
  hoas_identity: bool;  (* rule is absorbed by LP's HOAS — skip in emit *)
  intro_antecedent: bool; (* rule introduces an antecedent hyp (IMP4, ALL9…) *)
  branching: bool;      (* ALL7/XST8: first child is a _1 equality chain *)
}

let rules : (string, rule_info) Hashtbl.t =
  let t = Hashtbl.create 150 in
  let r ?(emit_args=None) ?(result_schema=1) ?(hoas_identity=false)
        ?(intro_antecedent=false) ?(branching=false) name arity =
    Hashtbl.replace t name
      { arity; emit_args; result_schema;
        hoas_identity; intro_antecedent; branching }
  in
  (* §A.1 Conjunction *)
  r "AND1" 2 ~result_schema:2;
  r "AND2" 1;
  r "AND3" 1;
  r "AND4" 2 ~result_schema:2;
  r "AND5" 1 ~emit_args:(Some "dynamic:and5");
  (* §A.2 Disjunction *)
  r "OR1" 1;
  r "OR2" 2 ~result_schema:2;
  r "OR3" 2 ~result_schema:2;
  r "OR4" 1;
  (* §A.3 Implication *)
  r "IMP1" 1;
  r "IMP2" 2 ~result_schema:2;
  r "IMP3" 2 ~result_schema:2;
  r "IMP4" 1 ~intro_antecedent:true;
  r "IMP5" 1;
  (* §A.4 Equivalence *)
  r "EQV1" 2 ~result_schema:2;
  r "EQV2" 2 ~result_schema:2;
  r "EQV3" 2 ~result_schema:2;
  r "EQV4" 2 ~result_schema:2;
  (* §A.5 Negation *)
  r "NOT1" 1;
  r "NOT2" 1;
  (* §A.6 Axioms *)
  let hyp = Some "dynamic:hyp" in
  r "AXM1" 0 ~emit_args:hyp ~result_schema:0;
  r "AXM2" 0 ~emit_args:hyp ~result_schema:0;
  r "AXM3" 0 ~emit_args:hyp ~result_schema:0;
  r "AXM4" 0 ~emit_args:hyp ~result_schema:0;
  r "AXM5" 0 ~emit_args:hyp ~result_schema:0;
  r "AXM6" 0 ~emit_args:hyp ~result_schema:0;
  r "AXM7" 0 ~result_schema:0;
  r "AXM8" 0 ~emit_args:(Some "dynamic:axm8") ~result_schema:0;
  r "AXM9" 0 ~emit_args:(Some "dynamic:axm9") ~result_schema:0;
  (* §A.7 Universal quantification *)
  let top_i = Some "\xe2\x8a\xa4\xe1\xb5\xa2" in (* ⊤ᵢ *)
  r "ALL1" 1 ~emit_args:top_i ~hoas_identity:true;
  r "ALL2" 1 ~emit_args:top_i ~hoas_identity:true;
  r "ALL3" 1 ~emit_args:top_i ~hoas_identity:true;
  r "ALL4" 1 ~emit_args:top_i ~hoas_identity:true;
  r "ALL5" 1;
  r "ALL6" 1 ~hoas_identity:true;
  r "ALL7" 2 ~emit_args:(Some "dynamic:all7") ~branching:true;
  r "ALL8" 1;
  r "ALL9" 1 ~intro_antecedent:true;
  (* §A.8 Existential quantification *)
  r "XST1" 1 ~emit_args:top_i ~hoas_identity:true;
  r "XST2" 1 ~emit_args:top_i ~hoas_identity:true;
  r "XST3" 1 ~emit_args:top_i ~hoas_identity:true;
  r "XST4" 1 ~emit_args:top_i ~hoas_identity:true;
  r "XST5" 1;
  r "XST51" 1;
  r "XST6" 1;
  r "XST61" 1;
  r "XST7" 1;
  r "XST8" 2 ~emit_args:(Some "dynamic:xst8") ~branching:true;
  (* §A.9-11 VR/FX/STOP/INS *)
  r "VR1" 0 ~result_schema:0;
  r "VR2" 1;
  r "VR3" 1;
  r "VR4" 0 ~result_schema:0;
  r "FX1" 1;
  r "FX2" 0 ~result_schema:0;
  r "FX3" 0 ~result_schema:0;
  r "STOP" 1;
  r "INS" 1;
  (* §A.12 Normalisation *)
  r "NRM1" 1;
  r "NRM2" 1;
  r "NRM3" 1;
  r "NRM4" 1;
  r "NRM5" 1;
  r "NRM6" 1;
  r "NRM7" 1;
  r "NRM8" 1 ~hoas_identity:true;
  r "NRM9" 1;
  r "NRM10" 1;
  r "NRM11" 1;
  r "NRM12" 1;
  r "NRM13" 1;
  r "NRM14" 1;
  r "NRM15" 1;
  r "NRM16" 0;
  r "NRM17" 1;
  r "NRM18" 1;
  r "NRM19" 0 ~emit_args:(Some "dynamic:nrm19");
  r "NRM20" 1;
  r "NRM21" 1;
  r "NRM22" 1;
  r "NRM23" 1;
  r "NRM24" 1;
  r "NRM25" 1;
  r "NRM26" 1;
  (* NRM27–30: arithmetic solver dispatch; not yet formalised in LP.
     Deliberately unregistered — replay_arity raises Ill_formed_replay
     (→ SKIP) if PP emits them, rather than silently dropping a step. *)
  (* §A.13 Equality *)
  r "EVR1" 0 ~result_schema:0;
  r "EVR2" 1;
  r "EVR3" 1;
  r "EVR4" 0 ~result_schema:0;
  r "EVR11" 0 ~result_schema:0;
  r "EAXM1" 0 ~emit_args:hyp ~result_schema:0;
  r "EAXM2" 0 ~emit_args:hyp ~result_schema:0;
  r "EAXM31" 1;
  r "EAXM32" 1;
  r "EIMP51" 1;
  r "EIMP52" 1;
  r "EAXM91" 1;
  r "EAXM92" 1;
  r "OPR1" 1 ~emit_args:(Some "dynamic:opr1");
  r "OPR2" 1 ~emit_args:(Some "dynamic:opr2");
  r "EQC1" 1;
  r "EQC2" 1;
  r "EQS1" 1;
  r "EQS2" 1;
  r "ECTR1" 0 ~result_schema:0;
  r "ECTR2" 0 ~result_schema:0;
  r "ECTR3" 0 ~result_schema:0;
  r "ECTR4" 0 ~result_schema:0;
  r "ECTR5" 0 ~result_schema:0;
  r "ECTR6" 0 ~result_schema:0;
  (* §A.14 Arithmetic *)
  r "AR1" 1;
  r "AR2" 0 ~emit_args:(Some "trust") ~result_schema:0;
  r "AR3" 1 ~emit_args:(Some "dynamic:ar3");
  r "AR3_F" 1 ~emit_args:top_i ~hoas_identity:true;
  r "AR4" 0 ~emit_args:(Some "dynamic:ar4") ~result_schema:0;
  r "AR5" 1 ~emit_args:(Some "dynamic:ar56");
  r "AR6" 1 ~emit_args:(Some "dynamic:ar56");
  r "AR7" 1 ~emit_args:(Some "dynamic:ar78");
  r "AR8" 1 ~emit_args:(Some "dynamic:ar78");
  r "AR9" 1 ~emit_args:(Some "dynamic:ar9");
  (* AR10 is a solver no-op: P = Q (trivially); the LP symbol in Arith.lp
     is never applied because PP emits AR10 only when Q = P. Phantom. *)
  r "AR10" (-1);
  r "AR11" 0 ~result_schema:0;
  r "AR12" 1 ~intro_antecedent:true;
  r "AR13" 1 ~emit_args:(Some "trust trust");
  (* §A.15 Boolean *)
  r "BOOL11" 1;
  r "BOOL12" 1;
  r "BOOL21" 1;
  r "BOOL22" 1;
  r "BOOL31" 1 ~emit_args:(Some "trust");
  r "BOOL32" 1 ~emit_args:(Some "trust");
  r "BOOL41" 1 ~emit_args:(Some "trust");
  r "BOOL42" 1 ~emit_args:(Some "trust");
  r "BOOL51" 0 ~result_schema:0;
  r "BOOL52" 0 ~result_schema:0;
  (* Phantom entries *)
  r "FIN" (-1);
  r "STOP_NORM" (-1);
  r "NRM" (-1);
  t

(* --- Lookup functions --- *)

let rule_arity name =
  match Hashtbl.find_opt rules name with
  | Some r -> r.arity
  | None ->
    failwith (Printf.sprintf "rule_db: unknown rule %S" name)

let emit_args name =
  match Hashtbl.find_opt rules name with
  | Some r -> r.emit_args
  | None -> None

let result_schema name =
  match Hashtbl.find_opt rules name with
  | Some r -> Some r.result_schema
  | None -> None

let lookup_flag f name =
  match Hashtbl.find_opt rules name with
  | Some r -> f r
  | None -> false

(* --- Rule-class predicates (queried by emit_lp / proof_tree). ---
   Predicates take the *base* name (after _1 / _N stripping): they only
   need to be set on the base rule in the db above. *)

let is_hoas_identity = lookup_flag (fun r -> r.hoas_identity)
let intro_antecedent = lookup_flag (fun r -> r.intro_antecedent)
let is_branching    = lookup_flag (fun r -> r.branching)

(* --- Rule-name string predicates ---
   PP replay rule names carry structural information in their suffix:

     FOO          — base rule (e.g. AND1, IMP4)
     FOO_1        — primed variant (appears inside a _1 equality chain
                    that precedes ALL7/XST8)
     FOO_N        — n-ary variant (e.g. ALL7_2, NRM1_3), N ≥ 2
     FOO_1_N      — primed + n-ary
     NRM<digit>…  — normalisation step

   The helpers here are the one authoritative parser of those suffixes.
   Downstream modules should call these instead of re-implementing
   substring checks. *)

(* Strip trailing _N where N is a non-empty digit string:
     ALL7_2      → ALL7
     ALL7_1_3    → ALL7_1
     ALL7_1      → ALL7_1   (not stripped, because "1" vs "_N" shape
                              is resolved by callers via is_primed)
   Note: we do strip _1 here unless it is the only suffix, because
   callers (is_primed) want to see the _1 after stripping an outer _N.
   The rule is: strip *one* trailing numeric suffix. *)
let strip_suffix rule =
  match String.rindex_opt rule '_' with
  | Some i when i > 0 && i < String.length rule - 1 ->
    let suffix = String.sub rule (i + 1) (String.length rule - i - 1) in
    if String.to_seq suffix |> Seq.for_all (fun c -> c >= '0' && c <= '9')
    then String.sub rule 0 i
    else rule
  | _ -> rule

(* Raw suffix check: name ends in "_1".
   Used when classifying a replay line. *)
let is_primed_name name =
  String.length name > 2 &&
  String.sub name (String.length name - 2) 2 = "_1"

(* Suffix check that sees through an outer n-ary wrapping:
     ALL7_1   → true
     ALL7_1_3 → true   (strip _3, then _1)
     ALL7_3   → false
   Used after select_variant has attached a _N tag. *)
let is_primed rule = is_primed_name (strip_suffix rule)

(* Extract the trailing n-ary count: ALL7_3 → 3, ALL7 → 1. *)
let nary_count rule =
  match String.rindex_opt rule '_' with
  | Some i when i > 0 && i < String.length rule - 1 ->
    let suffix = String.sub rule (i + 1) (String.length rule - i - 1) in
    (try int_of_string suffix with _ -> 1)
  | _ -> 1

(* NRM<digit>... (NRM1, NRM12, NRM1_1, …). Excludes the bare "NRM"
   phantom (arity -1). *)
let is_nrm_step name =
  String.length name > 3 &&
  String.sub name 0 3 = "NRM" &&
  (let c = name.[3] in c >= '0' && c <= '9')
