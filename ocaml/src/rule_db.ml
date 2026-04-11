(* Rule database: static metadata for PP inference rules. *)

type rule_info = {
  arity: int;           (* -1=phantom, 0=leaf, 1=single child, 2=two children *)
  emit_args: string option;
  result_schema: int;   (* 0=leaf/TRUE, 1=passthrough, 2=conjunction *)
  has_primed: bool;
}

let rules : (string, rule_info) Hashtbl.t =
  let t = Hashtbl.create 150 in
  let r ?(emit_args=None) ?(result_schema=1) ?(has_primed=true) name arity =
    Hashtbl.replace t name { arity; emit_args; result_schema; has_primed }
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
  r "IMP4" 1;
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
  r "ALL1" 1 ~emit_args:top_i;
  r "ALL2" 1 ~emit_args:top_i;
  r "ALL3" 1 ~emit_args:top_i;
  r "ALL4" 1 ~emit_args:top_i;
  r "ALL5" 1;
  r "ALL6" 1;
  r "ALL7" 2 ~emit_args:(Some "dynamic:all7");
  r "ALL8" 1;
  r "ALL9" 1;
  (* §A.8 Existential quantification *)
  r "XST1" 1 ~emit_args:top_i;
  r "XST2" 1 ~emit_args:top_i;
  r "XST3" 1 ~emit_args:top_i;
  r "XST4" 1 ~emit_args:top_i;
  r "XST5" 1;
  r "XST51" 1;
  r "XST6" 1;
  r "XST61" 1;
  r "XST7" 1;
  r "XST8" 2 ~emit_args:(Some "dynamic:xst8");
  (* §A.9-11 VR/FX/STOP/INS *)
  r "VR1" 0 ~result_schema:0;
  r "VR2" 1;
  r "VR3" 1;
  r "VR4" 0 ~result_schema:0;
  r "FX1" 1;
  r "FX2" 0 ~result_schema:0;
  r "FX3" 0 ~result_schema:0;
  r "STOP" 1;
  r "INS" 1 ~has_primed:false;
  (* §A.12 Normalisation *)
  r "NRM1" 1;
  r "NRM2" 1;
  r "NRM3" 1;
  r "NRM4" 1;
  r "NRM5" 1;
  r "NRM6" 1;
  r "NRM7" 1;
  r "NRM8" 1;
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
  r "NRM27" 1;
  r "NRM28" 1;
  r "NRM29" 1;
  r "NRM30" 1;
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
  r "AR3_F" 1 ~emit_args:top_i ~has_primed:false;
  r "AR4" 0 ~emit_args:(Some "dynamic:ar4") ~result_schema:0;
  r "AR5" 1 ~emit_args:(Some "dynamic:ar56");
  r "AR5_2" 1 ~emit_args:(Some "dynamic:ar56");
  r "AR6" 1 ~emit_args:(Some "dynamic:ar56");
  r "AR6_2" 1 ~emit_args:(Some "dynamic:ar56");
  r "AR7" 1 ~emit_args:(Some "dynamic:ar78");
  r "AR7_2" 1 ~emit_args:(Some "dynamic:ar78");
  r "AR8" 1 ~emit_args:(Some "dynamic:ar78");
  r "AR8_2" 1 ~emit_args:(Some "dynamic:ar78");
  r "AR9" 1 ~emit_args:(Some "dynamic:ar9");
  r "AR10" (-1) ~has_primed:false;
  r "AR11" 0 ~result_schema:0;
  r "AR12" 1;
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
  r "FIN" (-1) ~has_primed:false;
  r "STOP_NORM" (-1) ~has_primed:false;
  r "NRM" (-1) ~has_primed:false;
  t

(* --- Lookup functions --- *)

let find_opt name = Hashtbl.find_opt rules name

let rule_arity name =
  match Hashtbl.find_opt rules name with
  | Some r -> r.arity
  | None ->
    Printf.eprintf "warning: unknown rule %S, assuming arity 1\n" name;
    1

let has_primed name =
  match Hashtbl.find_opt rules name with
  | Some r -> r.has_primed
  | None -> true

let emit_args name =
  match Hashtbl.find_opt rules name with
  | Some r -> r.emit_args
  | None -> None

let result_schema name =
  match Hashtbl.find_opt rules name with
  | Some r -> Some r.result_schema
  | None -> None
