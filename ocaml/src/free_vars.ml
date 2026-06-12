open Syntax_pp

module SS = Set.Make(String)

type free_vars = { prop_vars: SS.t; exp_vars: SS.t }

let empty_fv = { prop_vars = SS.empty; exp_vars = SS.empty }

(* Reserved = LP library symbols PP refers to by name, so they're never collected
   as free vars to declare: the booleans, the set-equality predicate (`_eql_set` /
   `eql_set`), and the pair projections (`_pj1` / `_pj2`, rendered to the B.lp
   primitives `pj1` / `pj2` by pp_lp). *)
let reserved =
  SS.of_list ["VRAI"; "TRUE"; "FAUX"; "FALSE";
              "_eql_set"; "eql_set"; "_pj1"; "_pj2"; "pj1"; "pj2"]

let rec collect_exp_fv bound fv = function
  | Var s when SS.mem s bound || SS.mem s reserved -> fv
  | Var s -> { fv with exp_vars = SS.add s fv.exp_vars }
  | Nat _ -> fv
  | AOp (_, e1, e2) -> collect_exp_fv bound (collect_exp_fv bound fv e1) e2
  | Neg e -> collect_exp_fv bound fv e
  | App (f, args) ->            (* an applied function symbol is itself free (`τ ι`) *)
    let fv = if SS.mem f bound || SS.mem f reserved then fv
             else { fv with exp_vars = SS.add f fv.exp_vars } in
    List.fold_left (collect_exp_fv bound) fv args
  | SetImage (e1, e2) | Inter (e1, e2) | Union (e1, e2) | Range (e1, e2)
  | Maplet (e1, e2) | DomRestrict (e1, e2) | RanRestrict (e1, e2) ->
    collect_exp_fv bound (collect_exp_fv bound fv e1) e2
  | Inverse e -> collect_exp_fv bound fv e
  | SetLit es -> List.fold_left (collect_exp_fv bound) fv es

let rec collect_prd_fv bound fv = function
  | Lift (Var s) when SS.mem s bound ->
    { fv with exp_vars = SS.add s fv.exp_vars }
  | Lift (Var s) when SS.mem s reserved -> fv
  | Lift (Var s) ->
    { fv with prop_vars = SS.add s fv.prop_vars }
  | Lift (App (f, args)) ->
    let fv = if SS.mem f bound || SS.mem f reserved then fv
             else { fv with exp_vars = SS.add f fv.exp_vars } in
    List.fold_left (collect_exp_fv bound) fv args
  | Lift e -> collect_exp_fv bound fv e
  | Unary (_, p) -> collect_prd_fv bound fv p
  | Binary (_, p1, p2) ->
    collect_prd_fv bound (collect_prd_fv bound fv p1) p2
  | Bind (_, xs, body) ->
    let bound' = List.fold_left (fun s x -> SS.add x s) bound xs in
    collect_prd_fv bound' fv body
  | Eq (e1, e2) | Leq (e1, e2) ->
    collect_exp_fv bound (collect_exp_fv bound fv e1) e2
  | Mem (es, e) ->
    collect_exp_fv bound (List.fold_left (collect_exp_fv bound) fv es) e

let free_vars_of_prd p = collect_prd_fv SS.empty empty_fv p
