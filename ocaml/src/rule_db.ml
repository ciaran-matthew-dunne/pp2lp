(* Rule database: static metadata for PP inference rules.

   The trace includes both base rules (e.g. AND1) and primed/n-ary
   variants (e.g. AND1_1, ALL7_3, ALL7_1_3).  The metadata table is
   keyed on base names; the suffix helpers below decode the variants. *)

(** Kind of a derivation slot in a rule's signature.
    - [Con]: side-condition proof (a solver lemma or generated proof).
      Filled inline in the LP application; not a child in the proof tree.
    - [Seq]: sequent derivation — a regular proof-tree child.
    - [Res]: result derivation — a chain child.  Currently the first
      slot of branching quantifiers (ALL7/XST8). *)
type kind = Con | Seq | Res

(** [Arity slots]: the rule's argument-kind list. *)
type arity = Arity of kind list

(** How a rule's `refine` arguments are built.  This is the *single*
    dispatch key the emitter ([Translate]) matches on, exhaustively — so
    adding a constructor here forces a corresponding arm in the emitter
    or the build fails (warning 8 is enabled).  Replaces the former
    stringly-typed [emit_args] (e.g. ["dynamic:ar9"]), under which a
    dangling tag silently fell through to a wrong default. *)
type emit =
  | Default        (* generic: one hole per derivation slot *)
  | Trust_cons     (* Con-slot solver side-conditions with no generated proof:
                      emit fails loud rather than `trust` (AR13; unfired) *)
  | Hyp_search     (* find an in-scope hyp by goal-derived predicate (AXM1-6, EAXM1/2) *)
  | Witness_hyp    (* find a (witness, hyp) pair, children dropped (AXM9, NRM19) *)
  | Ins            (* universal-instantiation contradiction search *)
  | And5
  | Opr of bool    (* equality rewrite; [true] = right-to-left (OPR2) *)
  | Axm8
  | Nrm20 | Nrm21 | Nrm22 | Nrm23
  | Nrm26          (* binder drop at the slot PP names (`NRM26 k`, the slot read
                      off the annotation diff against the child's binder list) *)
  | Nrm2730        (* NRM27-30: trust-free solver dispatch — peel the pinned
                      binder at the witness `b`, ⊤-normalise the substituted
                      conjunction (see [Emit_ctx.nrm29_witness_bridge]).  One
                      lemma, NRM29; NRM27/28/30 fold onto it (untriggered) *)
  | Ar2            (* AR2: leaf `(leq a b) ⇒ R` with a > b concrete ℤ literals —
                      the ℤ-literal `AR2` lemma, closed by `λ k, k ⊤ᵢ` *)
  | Ar3 | Ar3_f | Ar4 | Ar5_6 | Ar7_8 | Ar9 | Ar10
  | Bool_split     (* BOOL31/32/41/42: discharge the `V ϵ BOOL` side-condition
                      from an injected typing hypothesis (Emit_ctx.bool_split_var) *)
  | Eqs2           (* EQS2: negated eql_set marker discharged via store evidence *)
  | Eimp5          (* EIMP51/52: `¬(E=F) ⇒ P` / `(E=F) ⇒ P` discharged with the
                      swapped-orientation equality hyp found in scope *)
  | Ectr           (* ECTR1-6: equality-substitution contradiction leaves *)
  | Arith          (* ARITH: solver ⊥-terminal — generated Farkas combination
                      of the in-scope ≤-hyps (see [Emit_ctx.find_arith_contradiction]) *)
  | Egalite        (* EGALITE: equality-prover ⊥-terminal — INS-style search
                      with hyps matched modulo the stored equalities *)

type rule_info = {
  arity: arity option;       (* None = phantom (skipped during trace processing). *)
  emit: emit;                (* how to build the rule's refine arguments *)
  hoas_identity: bool;       (* transformation is LP-definitional (ALL6: ¬Q ≡ Q⇒⊥);
                                parent and child goals convert, so skip to the child. *)
  intro_antecedent: bool;    (* rule introduces an antecedent hyp (IMP4, ALL9…) *)
  binds_var: bool;           (* rule introduces a tuple binder via `assume` (ALL8) *)
  chain_form: bool;          (* has a Res-chain `_1` lemma in lp/rules.  PP emits NRM
                                rules unprimed even inside result chains, so the emitter
                                primes them ([Emit_ctx.chain_emit_name]).  Set ONLY where
                                the `<name>_1` Res lemma actually exists — an unset NRM
                                rule reached in a chain fails loud (E_DISPATCH) instead of
                                emitting an undefined symbol lambdapi only catches later. *)
}

let rules : (string, rule_info) Hashtbl.t =
  let t = Hashtbl.create 150 in
  let r ?(emit=Default) ?(hoas_identity=false)
        ?(intro_antecedent=false) ?(binds_var=false) ?(chain_form=false) name arity =
    Hashtbl.replace t name
      { arity = Some arity; emit; hoas_identity;
        intro_antecedent; binds_var; chain_form }
  in
  let phantom name =
    Hashtbl.replace t name
      { arity = None; emit = Default; hoas_identity = false;
        intro_antecedent = false; binds_var = false;
        chain_form = false }
  in
  let leaf   = Arity [] in
  let pass   = Arity [Seq] in
  let conj   = Arity [Seq; Seq] in
  let branch = Arity [Res; Seq] in
  (* §A.1 Conjunction *)
  r "AND1" conj;
  r "AND2" pass;
  r "AND3" pass;
  r "AND4" conj;
  r "AND5" pass ~emit:And5;
  (* §A.2 Disjunction *)
  r "OR1" pass;
  r "OR2" conj;
  r "OR3" conj;
  r "OR4" pass;
  (* §A.3 Implication *)
  r "IMP1" pass;
  r "IMP2" conj;
  r "IMP3" conj;
  r "IMP4" pass ~intro_antecedent:true;
  r "IMP5" pass;
  (* §A.4 Equivalence *)
  r "EQV1" conj;
  r "EQV2" conj;
  r "EQV3" conj;
  r "EQV4" conj;
  (* §A.5 Negation *)
  r "NOT1" pass;
  r "NOT2" pass;
  (* §A.6 Axioms *)
  r "AXM1" leaf ~emit:Hyp_search;
  r "AXM2" leaf ~emit:Hyp_search;
  r "AXM3" leaf ~emit:Hyp_search;
  r "AXM4" leaf ~emit:Hyp_search;
  r "AXM5" leaf ~emit:Hyp_search;
  r "AXM6" leaf ~emit:Hyp_search;
  r "AXM7" leaf;
  r "AXM8" leaf ~emit:Axm8;
  r "AXM9" leaf ~emit:Witness_hyp;
  (* §A.7 Universal quantification.
     ALL1–4 are quantifier *regroupement* (§A.7): they merge `∀x·∀y·P` into the
     compound `∀(x,y)·P`.  They are plain `pass` rules, emitted for real (`refine
     ALLn _`, P inferred from the curried `!! w, !! y, P w y` conclusion in
     rules/All.lp); the goal renders with binders nested (flatten_binds is gone),
     and the take/drop premise reduces to the compound slot order downstream wants.
     ALL6 *is* LP-definitional (¬Q ≡ Q⇒⊥) → genuine [hoas_identity], still skipped. *)
  r "ALL1" pass;
  r "ALL2" pass;
  r "ALL3" pass;
  r "ALL4" pass;
  r "ALL5" pass;
  r "ALL6" pass ~hoas_identity:true;
  r "ALL7" branch;
  r "ALL8" pass ~binds_var:true;
  r "ALL9" pass ~intro_antecedent:true;
  (* §A.8 Existential quantification.  XST1–4 are the existential regroupement,
     emitted for real exactly like ALL1–4 (curried `_1`/base forms in rules/Xst.lp). *)
  r "XST1" pass;
  r "XST2" pass;
  r "XST3" pass;
  r "XST4" pass;
  r "XST5" pass;
  r "XST51" pass;
  r "XST6" pass;
  r "XST61" pass;
  r "XST7" pass;
  r "XST8" branch;
  (* §A.9-11 VR/FX/STOP/INS *)
  r "VR1" leaf;
  r "VR2" pass;
  r "VR3" pass;
  r "VR4" leaf;
  r "FX1" pass;
  r "FX2" leaf;
  r "FX3" leaf;
  r "STOP" pass;
  r "INS" pass ~emit:Ins;
  (* INS_BIS / FIN_INS: PP's instantiation phase records the chain of derived
     facts behind a multi-step INS contradiction explicitly (each FIN_INS(f)
     introduces an `__INSTANCIATION(f)` antecedent, discharged by the following
     IMP4).  The whole chain hangs off an [INS] node, whose dispatch reconstructs
     the contradiction by saturation and ignores the recorded subtree — so these
     only need to build (one Seq continuation each), never to emit. *)
  r "INS_BIS" pass;
  r "FIN_INS" pass;
  (* Solver terminals.  ARITH: the linear solver closes ⊥ with no recorded
     certificate; the emitter reconstructs a Farkas combination.  EGALITE:
     the equality prover rewrites the store's hyps along the stored
     equalities and re-promotes them as antecedents over ⊥ — the child
     proves that implication chain; the emitter supplies each rewritten
     antecedent as an ind_eq-transported hyp. *)
  r "ARITH" leaf ~emit:Arith;
  r "EGALITE" pass ~emit:Egalite;
  (* §A.12 Normalisation *)
  (* ~chain_form marks the NRM rules with a Res-chain `_1` lemma in lp/rules/Nrm.lp.
     PP emits all NRM rules unprimed in chains; the emitter primes only these and
     fails loud on the rest (keep in sync with the `symbol NRM<k>_1` set). *)
  r "NRM1" pass ~chain_form:true;
  r "NRM2" pass ~chain_form:true;   (* evidence-form NRM2_1 + translate.ml dispatch *)
  r "NRM3" pass ~chain_form:true;
  r "NRM4" pass ~chain_form:true;
  r "NRM5" pass ~chain_form:true;
  r "NRM6" pass ~chain_form:true;
  r "NRM7" pass ~chain_form:true;
  r "NRM8" pass ~chain_form:true;
  r "NRM9" pass ~chain_form:true;
  r "NRM10" pass ~chain_form:true;
  r "NRM11" pass ~chain_form:true;
  r "NRM12" pass ~chain_form:true;
  r "NRM13" pass ~chain_form:true;
  r "NRM14" pass ~chain_form:true;
  r "NRM15" pass ~chain_form:true;
  r "NRM16" leaf;
  r "NRM17" pass;
  r "NRM18" pass;
  r "NRM19" pass ~emit:Witness_hyp ~chain_form:true;
  r "NRM20" (Arity [Con; Seq]) ~emit:Nrm20 ~chain_form:true;  (* NRM20_1 postulate + translate.ml chain dispatch; soundness bridge deferred *)
  r "NRM21" (Arity [Con; Seq]) ~emit:Nrm21;
  r "NRM22" pass ~emit:Nrm22 ~chain_form:true;
  r "NRM23" pass ~emit:Nrm23 ~chain_form:true;
  r "NRM24" pass ~chain_form:true;
  r "NRM25" pass ~chain_form:true;
  r "NRM26" pass ~emit:Nrm26;
  (* Arithmetic-solver substitution: a conjunction holds [a + xᵢ ≤ 𝟎] and
     [b − xᵢ ≤ 𝟎] with solveur(a + b) = 𝟎, forcing xᵢ = b; substitute
     [xᵢ := b] and drop the binder.  NRM27/29 are the multi-binder (♡-block)
     forms, NRM28/30 the unary (♡x) forms; 27/28 are the xᵢ = 𝟎 specialisation
     (a = b = 𝟎).  Trust-free: the [Nrm2730] dispatch peels the binder at the
     reconstructed witness and ⊤-normalises the substituted conjunction
     ([Emit_ctx.nrm29_witness_bridge]).  Only NRM29 is corpus-triggered. *)
  r "NRM27" (Arity [Con; Seq]) ~emit:Nrm2730;
  r "NRM28" (Arity [Con; Seq]) ~emit:Nrm2730;
  r "NRM29" (Arity [Con; Seq]) ~emit:Nrm2730;
  r "NRM30" (Arity [Con; Seq]) ~emit:Nrm2730;
  (* §A.13 Equality *)
  r "EVR1" leaf;
  r "EVR2" pass;
  r "EVR3" pass;
  r "EVR4" leaf;
  r "EVR11" leaf;
  r "EAXM1" leaf ~emit:Hyp_search;
  r "EAXM2" leaf ~emit:Hyp_search;
  (* EAXM31/32: goal-closing leaves — the hyp is the goal's equality
     (resp. negated equality) commuted. *)
  r "EAXM31" leaf ~emit:Hyp_search;
  r "EAXM32" leaf ~emit:Hyp_search;
  r "EIMP51" pass ~emit:Eimp5;
  r "EIMP52" pass ~emit:Eimp5;
  r "EAXM91" pass;
  r "EAXM92" pass;
  r "OPR1" pass ~emit:(Opr false);
  r "OPR2" pass ~emit:(Opr true);
  r "EQC1" pass;
  r "EQC2" pass;
  r "EQS1" pass;
  r "EQS2" pass ~emit:Eqs2;
  r "ECTR1" leaf ~emit:Ectr;
  r "ECTR2" leaf ~emit:Ectr;
  r "ECTR3" leaf ~emit:Ectr;
  r "ECTR4" leaf ~emit:Ectr;
  r "ECTR5" leaf ~emit:Ectr;
  r "ECTR6" leaf ~emit:Ectr;
  (* §A.14 Arithmetic *)
  r "AR1" pass;
  r "AR2" (Arity [Con]) ~emit:Ar2;
  r "AR3" pass ~emit:Ar3;
  r "AR3_F" pass ~emit:Ar3_f;
  r "AR4" leaf ~emit:Ar4;
  r "AR5" pass ~emit:Ar5_6;
  r "AR6" pass ~emit:Ar5_6;
  r "AR7" pass ~emit:Ar7_8;
  r "AR8" pass ~emit:Ar7_8;
  r "AR9" pass ~emit:Ar9;
  r "AR10" (Arity [Con; Seq]) ~emit:Ar10;
  r "AR11" leaf;
  r "AR12" pass ~intro_antecedent:true;
  r "AR13" (Arity [Con; Con; Seq]) ~emit:Trust_cons;
  (* §A.15 Boolean *)
  r "BOOL11" pass;
  r "BOOL12" pass;
  r "BOOL21" pass;
  r "BOOL22" pass;
  r "BOOL31" (Arity [Con; Seq]) ~emit:Bool_split;
  r "BOOL32" (Arity [Con; Seq]) ~emit:Bool_split;
  r "BOOL41" (Arity [Con; Seq]) ~emit:Bool_split;
  r "BOOL42" (Arity [Con; Seq]) ~emit:Bool_split;
  r "BOOL51" leaf;
  r "BOOL52" leaf;
  (* Phantom entries *)
  phantom "FIN";
  phantom "STOP_NORM";
  phantom "NRM";
  t

(* --- Suffix decoding ----------------------------------------------- *)

(* PP rule names carry structural info in their suffix:
     FOO, FOO_1, FOO_N, FOO_1_N (N ≥ 2). *)

let strip_suffix rule =
  match String.rindex_opt rule '_' with
  | Some i when i > 0 && i < String.length rule - 1 ->
    let suffix = String.sub rule (i + 1) (String.length rule - i - 1) in
    if String.to_seq suffix |> Seq.for_all (fun c -> c >= '0' && c <= '9')
    then String.sub rule 0 i
    else rule
  | _ -> rule

let is_primed_name name =
  String.length name > 2 &&
  String.sub name (String.length name - 2) 2 = "_1"

let is_primed rule =
  match String.rindex_opt rule '_' with
  | Some i when i > 0 && i < String.length rule - 1 ->
    let suffix = String.sub rule (i + 1) (String.length rule - i - 1) in
    if String.to_seq suffix |> Seq.for_all (fun c -> c >= '0' && c <= '9')
    then suffix = "1" || is_primed_name (String.sub rule 0 i)
    else false
  | _ -> false

(* Trace rules use the suffixed form (FOO_1, FOO_3, FOO_1_3).  Look up
   metadata under the base name. *)
let base_of name =
  let s = strip_suffix name in
  if is_primed_name s then String.sub s 0 (String.length s - 2)
  else s

(* NRM family: the one rule group PP leaves *unprimed* inside a first-
   normalisation chain, so the emitter must add the `_1` Res form itself
   (see [Translate.chain_emit_name]).  Kept here so the name test lives
   with the other suffix/family classifiers, not inlined in translate.ml. *)
let is_nrm name =
  let b = base_of name in
  String.length b >= 3 && String.sub b 0 3 = "NRM"

let lookup name = Hashtbl.find_opt rules (base_of name)

(* --- Lookup helpers ------------------------------------------------ *)

let is_phantom name =
  match lookup name with
  | Some { arity = None; _ } -> true
  | Some _ -> false
  | None ->
    (* Unknown rules must NOT be silently filtered: that's how stack
       residual / "trace left N nodes" errors get swallowed.  Surface
       it as a tree-build error pointing at the offending rule. *)
    Errors.fail "E_UNKNOWN_RULE" "rule_db: unknown rule %S" name

(** Number of children the rule has in the proof tree
    (= number of [Seq] + [Res] slots).  [Con] slots are inline LP args
    rather than tree children.  Returns [-1] for phantom rules.
    Raises [Failure] if [name] is unknown. *)
let rule_arity name =
  (* STOP_1 is the leaf seed of an equality chain.  STOP itself is a
     proof step (single-child); the primed variant is arity 0. *)
  if name = "STOP_1" then 0
  else
    match lookup name with
    | Some { arity = Some (Arity slots); _ } ->
      List.length
        (List.filter (function Seq | Res -> true | Con -> false) slots)
    | Some { arity = None; _ } -> -1
    | None -> Errors.fail "E_UNKNOWN_RULE" "rule_db: unknown rule %S" name

let is_branching name =
  match lookup name with
  | Some { arity = Some (Arity slots); _ } ->
    List.exists (function Res -> true | _ -> false) slots
  | _ -> false

let slots name =
  if name = "STOP_1" then []
  else match lookup name with
  | Some { arity = Some (Arity slots); _ } -> slots
  | Some { arity = None; _ } -> []
  | None -> Errors.fail "E_UNKNOWN_RULE" "rule_db: unknown rule %S" name

(** The rule's emit strategy (defaults to [Default] for unknown names,
    which never reach the emitter — phantoms are filtered earlier). *)
let emit name =
  match lookup name with Some r -> r.emit | None -> Default

let lookup_flag f name =
  match lookup name with Some r -> f r | None -> false

let is_hoas_identity = lookup_flag (fun r -> r.hoas_identity)
let intro_antecedent = lookup_flag (fun r -> r.intro_antecedent)
let binds_var = lookup_flag (fun r -> r.binds_var)
let has_chain_form = lookup_flag (fun r -> r.chain_form)
