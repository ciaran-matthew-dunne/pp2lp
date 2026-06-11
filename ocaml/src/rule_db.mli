(* Rule database: static metadata for PP inference rules — the single
   source of truth for arity, suffix decoding, phantom status, and the
   emit strategy.  The backing table and the suffix-string helpers are
   internal; only the queries below are exposed. *)

(** Kind of a derivation slot in a rule's signature.
    - [Con]: side-condition proof (a `trust` arg or solver lemma), filled
      inline in the LP application; not a proof-tree child.
    - [Seq]: sequent derivation — a regular proof-tree child.
    - [Res]: result-chain child (the first slot of branching ALL7/XST8). *)
type kind = Con | Seq | Res

(** How a rule's `refine` arguments are built — the dispatch key matched
    exhaustively by [Rule_emit].  Adding a constructor forces a handling
    arm there (warning 8 is fatal). *)
type emit =
  | Default
  | Trust_cons
  | Hyp_search
  | Witness_hyp
  | Ins
  | And5
  | Opr of bool
  | Axm8
  | Nrm20 | Nrm21 | Nrm22 | Nrm23
  | Nrm26
  | Nrm2730
  | Ar2
  | Ar3 | Ar3_f | Ar4 | Ar5_6 | Ar7_8 | Ar9 | Ar10
  | Bool_split
  | Eqs2
  | Ectr
  | Arith
  | Egalite

(** Metadata base name: strips primed/n-ary suffixes (FOO_1, FOO_3,
    FOO_1_3 ↦ FOO). *)
val base_of : string -> string

(** Is [rule] a primed (Res-typed) variant — FOO_1 or FOO_1_N? *)
val is_primed : string -> bool

(** Is [rule] in the NRM family? *)
val is_nrm : string -> bool

(** Is [rule] a phantom (normalisation marker, skipped during tree build)?
    Raises [Failure] on an unknown rule rather than silently filtering. *)
val is_phantom : string -> bool

(** Number of proof-tree children (= [Seq] + [Res] slots; [Con] slots are
    inline args).  Raises [Failure] on an unknown rule. *)
val rule_arity : string -> int

(** Does the rule have a [Res] slot (ALL7 / XST8)? *)
val is_branching : string -> bool

(** The rule's full slot-kind list.  Raises [Failure] on an unknown rule. *)
val slots : string -> kind list

(** The rule's emit strategy ([Default] for unknown names). *)
val emit : string -> emit

(** Is the rule absorbed by LP's HOAS (skipped in emit)? *)
val is_hoas_identity : string -> bool

(** Does the rule introduce an antecedent hypothesis (IMP4, ALL9, AR12)? *)
val intro_antecedent : string -> bool

(** Does the rule introduce a tuple binder via `assume` (ALL8)? *)
val binds_var : string -> bool
