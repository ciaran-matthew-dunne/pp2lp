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
  match ctx.entries with
  | (neg_name, Unary (Not, p)) :: _ ->
    begin match find_hyp ctx p with
    | Some pos_name -> Some (neg_name, pos_name)
    | None -> None
    end
  | (neg_name, Binary (Imp, p, _)) :: _ ->
    begin match find_hyp ctx p with
    | Some pos_name -> Some (neg_name, pos_name)
    | None -> None
    end
  | _ -> None

(* Wildcard-aware structural comparison.
   Variables in the wildcards set, or containing '$', match anything. *)
let rec exp_matches wildcards pat hyp =
  match pat, hyp with
  | Var v, _ when SS.mem v wildcards || String.contains v '$' -> true
  | Var a, Var b -> a = b
  | Nat a, Nat b -> a = b
  | App (f1, a1), App (f2, a2) ->
    f1 = f2 && List.length a1 = List.length a2 &&
    List.for_all2 (exp_matches wildcards) a1 a2
  | AOp (o1, a1, b1), AOp (o2, a2, b2) ->
    o1 = o2 && exp_matches wildcards a1 a2 && exp_matches wildcards b1 b2
  | Neg e1, Neg e2 -> exp_matches wildcards e1 e2
  | SetImage (a1, b1), SetImage (a2, b2)
  | Inter (a1, b1), Inter (a2, b2)
  | Union (a1, b1), Union (a2, b2) ->
    exp_matches wildcards a1 a2 && exp_matches wildcards b1 b2
  | _ -> false
and prd_matches wildcards pat hyp =
  match pat, hyp with
  | Lift e1, Lift e2 -> exp_matches wildcards e1 e2
  | Unary (o1, p1), Unary (o2, p2) -> o1 = o2 && prd_matches wildcards p1 p2
  | Binary (o1, a1, b1), Binary (o2, a2, b2) ->
    o1 = o2 && prd_matches wildcards a1 a2 && prd_matches wildcards b1 b2
  | Bind (b1, _, body1), Bind (b2, _, body2) ->
    b1 = b2 && prd_matches wildcards body1 body2
  | Mem (es1, e1), Mem (es2, e2) ->
    List.length es1 = List.length es2 &&
    List.for_all2 (exp_matches wildcards) es1 es2 && exp_matches wildcards e1 e2
  | Eq (a1, b1), Eq (a2, b2)
  | Leq (a1, b1), Leq (a2, b2) ->
    exp_matches wildcards a1 a2 && exp_matches wildcards b1 b2
  | _ -> false

let ins_heart_resolve ctx =
  let rec count_bind_vars = function
    | Bind (Forall2, xs, inner) ->
      List.length xs + count_bind_vars inner
    | _ -> 0
  in
  let rec collect_bind_vars = function
    | Bind (Forall2, xs, inner) ->
      List.fold_right SS.add xs (collect_bind_vars inner)
    | _ -> SS.empty
  in
  let rec extract_neg_body = function
    | Bind (Forall2, _, inner) -> extract_neg_body inner
    | Unary (Not, body) -> Some body
    | _ -> None
  in
  let find_matching_hyps wildcards leaves entries =
    let find_match leaf =
      List.find_opt (fun (_, p) ->
        (match leaf with Leq _ -> false | _ -> true) &&
        prd_matches wildcards leaf p
      ) entries
    in
    let rec go acc = function
      | [] -> Some (List.rev acc)
      | leaf :: rest ->
        match find_match leaf with
        | Some (name, _) -> go (name :: acc) rest
        | None -> None
    in
    go [] leaves
  in
  let build_term heart n_vars conjs =
    let conj_term = match conjs with
      | [] -> assert false
      | first :: rest ->
        List.fold_left (fun acc c ->
          Printf.sprintf "(\xe2\x88\xa7\xe1\xb5\xa2 %s %s)" acc c (* ∧ᵢ *)
        ) first rest
    in
    let underscores = String.concat "" (List.init n_vars (fun _ -> " _")) in
    Printf.sprintf "%s%s %s" heart underscores conj_term
  in
  (* Collect all non-∀₂ entries as potential conjunct matches *)
  let other_entries = List.filter (fun (_, p) ->
    match p with Bind (Forall2, _, _) -> false | _ -> true
  ) ctx.entries in
  let rec scan = function
    | [] -> None
    | (name, (Bind (Forall2, _, _) as p)) :: rest ->
      let n_vars = count_bind_vars p in
      let wildcards = collect_bind_vars p in
      begin match extract_neg_body p with
      | Some body ->
        let leaves = conj_leaves body in
        begin match find_matching_hyps wildcards leaves other_entries with
        | Some conjs when conjs <> [] ->
          Some (build_term name n_vars conjs)
        | _ -> scan rest
        end
      | None -> scan rest
      end
    | _ :: rest -> scan rest
  in
  scan ctx.entries

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
      raise (Proof_tree.Emit_admit "INS could not resolve contradiction")
