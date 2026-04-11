open Syntax_pp

let rec collect_conj_hyps acc = function
  | Binary (And, l, r) ->
    collect_conj_hyps (collect_conj_hyps acc l) r
  | p -> p :: acc

let rec extract_theorem_hyps = function
  | Bind (Bang, _, body) -> extract_theorem_hyps body
  | Binary (Imp, hyps, _) -> collect_conj_hyps [] hyps
  | _ -> []

type hyp_ctx = {
  entries: (string * prd) list;
  counter: int;
}

let empty_ctx = { entries = []; counter = 0 }

let fresh_hyp ctx p =
  let name = Printf.sprintf "h%d" ctx.counter in
  let ctx' = { entries = (name, p) :: ctx.entries;
               counter = ctx.counter + 1 } in
  (name, ctx')

let find_hyp ctx target =
  let rec search = function
    | [] -> None
    | (name, p) :: rest ->
      if p = target then Some name else search rest
  in
  search ctx.entries
