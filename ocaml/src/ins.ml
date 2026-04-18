(* INS contradiction resolution.

   INS rules derive ⊥ from the current hypothesis context. Two strategies:
   1. Simple: find a ¬P paired with P among the most recent hypotheses.
   2. Heart:  find a ♡-hyp ∀₂ xs. ¬(C₁ ∧ … ∧ Cₙ) whose conjuncts all
              match something in the context (with the quantifier
              variables acting as wildcards). *)

open Syntax_pp
open Pp_lp
open Free_vars
open Hyp_ctx

let ins_simple_resolve ctx =
  List.find_map (fun (neg_name, hyp) ->
    match hyp with
    | Unary (Not, p)
    | Binary (Imp, p, _) ->
      (match find_hyp ctx p with
       | Some pos_name -> Some (neg_name, pos_name)
       | None -> None)
    | _ -> None
  ) ctx.entries

(* Flatten an arithmetic expression to a multiset of signed atomic terms.
   a + b - c → [(+, a); (+, b); (-, c)]
   -(a - b) → [(-, a); (+, b)]
   Anything non-arithmetic (Var, App, etc.) becomes a single atom. *)
let flatten_arith e =
  let rec go acc sign = function
    | AOp (Add, a, b) -> go (go acc sign a) sign b
    | AOp (Sub, a, b) -> go (go acc sign a) (not sign) b
    | Neg a -> go acc (not sign) a
    | atom -> (sign, atom) :: acc
  in
  go [] true e

(* True if the expression is a pure arithmetic combinator at its root. *)
let is_arith = function
  | AOp _ | Neg _ -> true
  | _ -> false

(* Substitution: wildcard name → concrete expression. *)
type subst = (string * exp) list

(* Match state: substitution + "arith_used" flag. We track whether any
   match path required flatten_arith multiset matching, because if so
   the instantiated pattern will be AST-different from the hyp and LP
   won't unify them. In that case the caller emits `trust` for the
   conjunct instead of the hyp name. *)
type state = { sub: subst; arith: bool }

let init_state = { sub = []; arith = false }

let extend_state st v e =
  match List.assoc_opt v st.sub with
  | Some e' -> if e' = e then Some st else None
  | None -> Some { st with sub = (v, e) :: st.sub }

(* Wildcard-aware structural comparison with substitution tracking.
   Returns Some state' on match, None otherwise. *)
let rec exp_matches wildcards st pat hyp =
  match pat, hyp with
  | Var v, _ when SS.mem v wildcards -> extend_state st v hyp
  | Var v, _ when String.contains v '$' ->
    (* Bare PP internals (e.g. x$3 in hypothesis form): treat as free. *)
    Some st
  | Var a, Var b -> if a = b then Some st else None
  | Nat a, Nat b -> if a = b then Some st else None
  | App (f1, a1), App (f2, a2)
    when f1 = f2 && List.length a1 = List.length a2 ->
    fold_match (exp_matches wildcards) st a1 a2
  | (AOp _ | Neg _), _ | _, (AOp _ | Neg _) when is_arith pat || is_arith hyp ->
    arith_matches wildcards st pat hyp
  | SetImage (a1, b1), SetImage (a2, b2)
  | Inter (a1, b1), Inter (a2, b2)
  | Union (a1, b1), Union (a2, b2) ->
    (match exp_matches wildcards st a1 a2 with
     | Some s -> exp_matches wildcards s b1 b2
     | None -> None)
  | _ -> None

and fold_match f st xs ys =
  match xs, ys with
  | [], [] -> Some st
  | x :: xs', y :: ys' ->
    (match f st x y with
     | Some s -> fold_match f s xs' ys'
     | None -> None)
  | _ -> None

and arith_matches wildcards st pat hyp =
  (* Mark arith-used so the caller can decide whether a trust bridge is
     needed (LP lacks arithmetic associativity/commutativity, so a hyp
     `-f - g + x` won't unify with a pattern `-f + x - g` even when both
     flatten to the same multiset). *)
  let st = { st with arith = true } in
  let pa = flatten_arith pat in
  let ha = flatten_arith hyp in
  if List.length pa <> List.length ha then None
  else
    let atom_match st (s1, e1) (s2, e2) =
      if s1 <> s2 then None else exp_matches wildcards st e1 e2
    in
    let rec consume st pats hyps =
      match pats with
      | [] -> if hyps = [] then Some st else None
      | p :: rest ->
        let rec pick seen = function
          | [] -> None
          | h :: hs ->
            (match atom_match st p h with
             | Some st' ->
               (match consume st' rest (List.rev_append seen hs) with
                | Some _ as r -> r
                | None -> pick (h :: seen) hs)
             | None -> pick (h :: seen) hs)
        in
        pick [] hyps
    in
    consume st pa ha

and prd_matches wildcards st pat hyp =
  match pat, hyp with
  | Lift e1, Lift e2 -> exp_matches wildcards st e1 e2
  | Unary (o1, p1), Unary (o2, p2) when o1 = o2 ->
    prd_matches wildcards st p1 p2
  | Binary (o1, a1, b1), Binary (o2, a2, b2) when o1 = o2 ->
    (match prd_matches wildcards st a1 a2 with
     | Some s -> prd_matches wildcards s b1 b2
     | None -> None)
  | Bind (b1, _, body1), Bind (b2, _, body2) when b1 = b2 ->
    prd_matches wildcards st body1 body2
  | Mem (es1, e1), Mem (es2, e2)
    when List.length es1 = List.length es2 ->
    (match fold_match (exp_matches wildcards) st es1 es2 with
     | Some s -> exp_matches wildcards s e1 e2
     | None -> None)
  | Eq (a1, b1), Eq (a2, b2)
  | Leq (a1, b1), Leq (a2, b2) ->
    (match exp_matches wildcards st a1 a2 with
     | Some s -> exp_matches wildcards s b1 b2
     | None -> None)
  | _ -> None

let ins_heart_resolve ctx =
  let rec collect_bind_vars_ordered = function
    | Bind (Forall2, xs, inner) ->
      xs @ collect_bind_vars_ordered inner
    | _ -> []
  in
  let rec extract_neg_body = function
    | Bind (Forall2, _, inner) -> extract_neg_body inner
    | Unary (Not, body) -> Some body
    | _ -> None
  in
  (* Try to match all leaves against hyp entries, accumulating substitution.
     Returns Some (subst, [(name_or_trust, used_arith); ...]) on success.
     Each entry records whether the leaf match needed arithmetic
     flattening: if yes, emit `trust` (LP cannot reassociate/commute
     arithmetic AST) else emit the hypothesis name. *)
  let find_matching_hyps wildcards leaves entries =
    let rec go st acc = function
      | [] -> Some (st.sub, List.rev acc)
      | leaf :: rest ->
        let rec try_entries = function
          | [] -> None
          | (name, p) :: es ->
            let base_arith = st.arith in
            let attempt = prd_matches wildcards {st with arith = false} leaf p in
            (match attempt with
             | Some st' ->
               let entry = (name, st'.arith) in
               let merged = { st' with arith = base_arith || st'.arith } in
               (match go merged (entry :: acc) rest with
                | Some _ as r -> r
                | None -> try_entries es)
             | None -> try_entries es)
        in
        try_entries entries
    in
    go init_state [] leaves
  in
  (* Pretty-print expressions to the buffer used by rules.
     We use LP syntax directly here. *)
  let pp_instantiation sub xs =
    let buf = Buffer.create 64 in
    List.iter (fun x ->
      Buffer.add_char buf ' ';
      match List.assoc_opt x sub with
      | Some e ->
        Buffer.add_char buf '(';
        Pp_lp.pp_exp buf e;
        Buffer.add_char buf ')'
      | None ->
        Buffer.add_char buf '_'
    ) xs;
    Buffer.contents buf
  in
  let build_term heart xs sub conjs =
    let proofs = List.map (fun (name, used_arith) ->
      if used_arith then "trust" else name
    ) conjs in
    let conj_term = match proofs with
      | [] -> assert false
      | first :: rest ->
        List.fold_left (fun acc c ->
          Printf.sprintf "(\xe2\x88\xa7\xe1\xb5\xa2 %s %s)" acc c (* ∧ᵢ *)
        ) first rest
    in
    Printf.sprintf "%s%s %s" heart (pp_instantiation sub xs) conj_term
  in
  (* Collect all non-∀₂ entries as potential conjunct matches *)
  let other_entries = List.filter (fun (_, p) ->
    match p with Bind (Forall2, _, _) -> false | _ -> true
  ) ctx.entries in
  let rec scan = function
    | [] -> None
    | (name, (Bind (Forall2, _, _) as p)) :: rest ->
      let xs = collect_bind_vars_ordered p in
      let wildcards = List.fold_right SS.add xs SS.empty in
      begin match extract_neg_body p with
      | Some body ->
        let leaves = conj_leaves body in
        begin match find_matching_hyps wildcards leaves other_entries with
        | Some (sub, conjs) when conjs <> [] ->
          Some (build_term name xs sub conjs)
        | _ -> scan rest
        end
      | None -> scan rest
      end
    | _ :: rest -> scan rest
  in
  scan ctx.entries

let debug_ctx = ref false

let dump_ctx ctx =
  Printf.eprintf "=== INS context (%d entries) ===\n" (List.length ctx.entries);
  List.iter (fun (name, p) ->
    Printf.eprintf "  %s: %s\n" name (Emit_pp.prd_to_pp p)
  ) ctx.entries

let emit_ins buf first_pad ctx =
  match ins_simple_resolve ctx with
  | Some (neg_name, pos_name) ->
    Buffer.add_string buf first_pad;
    Buffer.add_string buf "refine ";
    Buffer.add_string buf neg_name;
    Buffer.add_char buf ' ';
    Buffer.add_string buf pos_name
  | None ->
    match ins_heart_resolve ctx with
    | Some term ->
      Buffer.add_string buf first_pad;
      Buffer.add_string buf "refine ";
      Buffer.add_string buf term
    | None ->
      if !debug_ctx then dump_ctx ctx;
      raise (Proof_tree.Emit_admit "INS could not resolve contradiction")
