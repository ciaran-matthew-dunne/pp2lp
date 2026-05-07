open Syntax_pp

type hyp_ctx = {
  entries: (string * prd) list;
  (* Tuple-typed binders introduced via `assume <name>;` (most recent
     first). Each entry is `(binder_name, [x_0; x_1; ...; x_{n-1}])`
     where `x_k` is the original PP variable name that should resolve
     to `prj k binder_name` inside the body. Used by AXM9/NRM19 to find
     an in-scope Tuple-n witness, and by [tuple_subst_*] below to
     rewrite PP-original references that appear in rule arguments. *)
  tuple_binders: (string * string list) list;
  counter: int;
}

let empty_ctx = { entries = []; tuple_binders = []; counter = 0 }

let fresh_hyp ctx p =
  let name = Printf.sprintf "h%d" ctx.counter in
  let ctx' = { ctx with entries = (name, p) :: ctx.entries;
                        counter = ctx.counter + 1 } in
  (name, ctx')

let push_tuple_binder ctx name vars =
  { ctx with tuple_binders = (name, vars) :: ctx.tuple_binders }

let find_tuple_binder ctx arity =
  List.find_opt (fun (_, vs) -> List.length vs = arity) ctx.tuple_binders

(* Apply every in-scope tuple binder's projection substitution to an
   expression / predicate. Most-recent-first iteration in [tuple_binders]
   means inner binders are applied before outer, so inner shadowing wins:
   once a [Var x] is rewritten to [Prj _], outer passes leave it alone. *)
let tuple_subst_exp ctx e =
  List.fold_left (fun e (vname, vars) ->
    let e, _ = List.fold_left (fun (acc, k) x ->
      (Subst.subst_exp_to_prj x k vname acc, k + 1)
    ) (e, 0) vars in
    e
  ) e ctx.tuple_binders

(* As [tuple_subst_prd] but skip variables in [excludes] (kept as
   [Var]s so they can bind to enclosing λ / ∀ being constructed at the
   call site). *)
let tuple_subst_prd_excluding ctx excludes p =
  List.fold_left (fun p (vname, vars) ->
    let p, _ = List.fold_left (fun (b, k) x ->
      let b' = if List.mem x excludes then b
               else Subst.subst_prd_to_prj x k vname b in
      (b', k + 1)
    ) (p, 0) vars in
    p
  ) p ctx.tuple_binders

let tuple_subst_prd ctx p = tuple_subst_prd_excluding ctx [] p

let find_hyp ctx target =
  let rec search = function
    | [] -> None
    | (name, p) :: rest ->
      if p = target then Some name else search rest
  in
  search ctx.entries
