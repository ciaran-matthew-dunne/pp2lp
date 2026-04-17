open Syntax_pp

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
