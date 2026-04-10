(* Rule database: static metadata for PP inference rules.
   Previously loaded from data/rules.json; now inlined. *)

(* Rule arity: -1=skip, 0=leaf, 1=single child, 2=two children *)
let arity_tbl : (string, int) Hashtbl.t =
  let t = Hashtbl.create 150 in
  List.iter (fun (k,v) -> Hashtbl.replace t k v) [
    "AND1", 2; "AND2", 1; "AND3", 1; "AND4", 2; "AND5", 1;
    "OR1", 1; "OR2", 2; "OR3", 2; "OR4", 1;
    "IMP1", 1; "IMP2", 2; "IMP3", 2; "IMP4", 1; "IMP5", 1;
    "EQV1", 2; "EQV2", 2; "EQV3", 2; "EQV4", 2;
    "NOT1", 1; "NOT2", 1;
    "AXM1", 0; "AXM2", 0; "AXM3", 0; "AXM4", 0;
    "AXM5", 0; "AXM6", 0; "AXM7", 0; "AXM8", 0; "AXM9", 0;
    "ALL1", 1; "ALL2", 1; "ALL3", 1; "ALL4", 1;
    "ALL5", 1; "ALL6", 1; "ALL7", 2; "ALL8", 1; "ALL9", 1;
    "XST1", 1; "XST2", 1; "XST3", 1; "XST4", 1;
    "XST5", 1; "XST51", 1; "XST6", 1; "XST61", 1;
    "XST7", 1; "XST8", 2;
    "VR1", 0; "VR2", 1; "VR3", 1; "VR4", 0;
    "FX1", 1; "FX2", 0; "FX3", 0;
    "STOP", 1; "INS", 1;
    "NRM1", 1; "NRM2", 1; "NRM3", 1; "NRM4", 1;
    "NRM5", 1; "NRM6", 1; "NRM7", 1; "NRM8", 1;
    "NRM9", 1; "NRM10", 1; "NRM11", 1; "NRM12", 1;
    "NRM13", 1; "NRM14", 1; "NRM15", 1; "NRM16", 0;
    "NRM17", 1; "NRM18", 1; "NRM19", 0; "NRM20", 1;
    "NRM21", 1; "NRM22", 1; "NRM23", 1; "NRM24", 1;
    "NRM25", 1; "NRM26", 1; "NRM27", 1; "NRM28", 1;
    "NRM29", 1; "NRM30", 1;
    "EVR1", 0; "EVR2", 1; "EVR3", 1; "EVR4", 0; "EVR11", 0;
    "EAXM1", 0; "EAXM2", 0; "EAXM31", 1; "EAXM32", 1;
    "EIMP51", 1; "EIMP52", 1; "EAXM91", 1; "EAXM92", 1;
    "OPR1", 1; "OPR2", 1;
    "EQC1", 1; "EQC2", 1; "EQS1", 1; "EQS2", 1;
    "ECTR1", 0; "ECTR2", 0; "ECTR3", 0;
    "ECTR4", 0; "ECTR5", 0; "ECTR6", 0;
    "AR1", 1; "AR2", 0; "AR3", 1; "AR3_F", 1;
    "AR4", 0; "AR5", 1; "AR5_2", 1; "AR6", 1; "AR6_2", 1;
    "AR7", 1; "AR7_2", 1; "AR8", 1; "AR8_2", 1;
    "AR9", 1; "AR10", -1; "AR11", 0; "AR12", 1; "AR13", 1;
    "BOOL11", 1; "BOOL12", 1; "BOOL21", 1; "BOOL22", 1;
    "BOOL31", 1; "BOOL32", 1; "BOOL41", 1; "BOOL42", 1;
    "BOOL51", 0; "BOOL52", 0;
    "FIN", -1; "STOP_NORM", -1; "NRM", -1;
  ]; t

(* Rules without primed variants *)
let no_primed : (string, unit) Hashtbl.t =
  let t = Hashtbl.create 10 in
  List.iter (fun k -> Hashtbl.replace t k ()) [
    "INS"; "AR3_F"; "FIN"; "STOP_NORM"; "NRM";
  ]; t

(* Emit args for rules that need them *)
let emit_args_tbl : (string, string) Hashtbl.t =
  let t = Hashtbl.create 40 in
  List.iter (fun (k,v) -> Hashtbl.replace t k v) [
    "AND5", "dynamic:and5";
    "AXM1", "dynamic:hyp"; "AXM2", "dynamic:hyp";
    "AXM3", "dynamic:hyp"; "AXM4", "dynamic:hyp";
    "AXM5", "dynamic:hyp"; "AXM6", "dynamic:hyp";
    "AXM8", "dynamic:axm8"; "AXM9", "dynamic:axm9";
    "EAXM1", "dynamic:hyp"; "EAXM2", "dynamic:hyp";
    "ALL1", "\xe2\x8a\xa4\xe1\xb5\xa2"; "ALL2", "\xe2\x8a\xa4\xe1\xb5\xa2";
    "ALL3", "\xe2\x8a\xa4\xe1\xb5\xa2"; "ALL4", "\xe2\x8a\xa4\xe1\xb5\xa2";
    "ALL7", "dynamic:all7";
    "XST1", "\xe2\x8a\xa4\xe1\xb5\xa2"; "XST2", "\xe2\x8a\xa4\xe1\xb5\xa2";
    "XST3", "\xe2\x8a\xa4\xe1\xb5\xa2"; "XST4", "\xe2\x8a\xa4\xe1\xb5\xa2";
    "XST8", "dynamic:xst8";
    "NRM19", "dynamic:nrm19";
    "OPR1", "dynamic:opr1"; "OPR2", "dynamic:opr2";
    "AR2", "trust"; "AR3", "dynamic:ar3"; "AR3_F", "\xe2\x8a\xa4\xe1\xb5\xa2";
    "AR4", "dynamic:ar4";
    "AR5", "dynamic:ar56"; "AR6", "dynamic:ar56";
    "AR7", "dynamic:ar78"; "AR8", "dynamic:ar78";
    "AR9", "dynamic:ar9"; "AR13", "trust trust";
    "BOOL31", "trust"; "BOOL32", "trust";
    "BOOL41", "trust"; "BOOL42", "trust";
  ]; t

(* Result schema: 0=leaf/TRUE, 1=passthrough, 2=conjunction *)
let result_schema_tbl : (string, int) Hashtbl.t =
  let t = Hashtbl.create 150 in
  List.iter (fun (k,v) -> Hashtbl.replace t k v) [
    "AND1", 2; "AND2", 1; "AND3", 1; "AND4", 2; "AND5", 1;
    "OR1", 1; "OR2", 2; "OR3", 2; "OR4", 1;
    "IMP1", 1; "IMP2", 2; "IMP3", 2; "IMP4", 1; "IMP5", 1;
    "EQV1", 2; "EQV2", 2; "EQV3", 2; "EQV4", 2;
    "NOT1", 1; "NOT2", 1;
    "AXM1", 0; "AXM2", 0; "AXM3", 0; "AXM4", 0;
    "AXM5", 0; "AXM6", 0; "AXM7", 0; "AXM8", 0; "AXM9", 0;
    "ALL1", 1; "ALL2", 1; "ALL3", 1; "ALL4", 1;
    "ALL5", 1; "ALL6", 1; "ALL7", 1; "ALL8", 1; "ALL9", 1;
    "XST1", 1; "XST2", 1; "XST3", 1; "XST4", 1;
    "XST5", 1; "XST51", 1; "XST6", 1; "XST61", 1;
    "XST7", 1; "XST8", 1;
    "VR1", 0; "VR2", 1; "VR3", 1; "VR4", 0;
    "FX1", 1; "FX2", 0; "FX3", 0;
    "STOP", 1;
    "EVR1", 0; "EVR2", 1; "EVR3", 1; "EVR4", 0; "EVR11", 0;
    "EAXM1", 0; "EAXM2", 0; "EAXM31", 1; "EAXM32", 1;
    "EIMP51", 1; "EIMP52", 1; "EAXM91", 1; "EAXM92", 1;
    "OPR1", 1; "OPR2", 1;
    "EQC1", 1; "EQC2", 1; "EQS1", 1; "EQS2", 1;
    "ECTR1", 0; "ECTR2", 0; "ECTR3", 0;
    "ECTR4", 0; "ECTR5", 0; "ECTR6", 0;
    "AR1", 1; "AR2", 0; "AR3", 1; "AR3_F", 1;
    "AR4", 0; "AR5", 1; "AR5_2", 1; "AR6", 1; "AR6_2", 1;
    "AR7", 1; "AR7_2", 1; "AR8", 1; "AR8_2", 1;
    "AR9", 1; "AR10", 1; "AR11", 0; "AR12", 1;
    "BOOL11", 1; "BOOL12", 1; "BOOL21", 1; "BOOL22", 1;
    "BOOL31", 1; "BOOL32", 1; "BOOL41", 1; "BOOL42", 1;
    "BOOL51", 0; "BOOL52", 0;
  ]; t

(* --- Lookup functions --- *)

let rule_arity name =
  match Hashtbl.find_opt arity_tbl name with
  | Some a -> a
  | None ->
    Printf.eprintf "warning: unknown rule %S, assuming arity 1\n" name;
    1

let has_primed name =
  not (Hashtbl.mem no_primed name)

let emit_args name =
  Hashtbl.find_opt emit_args_tbl name

let result_schema name =
  Hashtbl.find_opt result_schema_tbl name
