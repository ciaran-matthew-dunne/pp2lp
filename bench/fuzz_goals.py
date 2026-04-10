#!/usr/bin/env python3
"""
Randomly generate FOL formulas and output as PP goals.

No validation — just generate and let PP and cvc5 both try them.
Comparison happens downstream.

Usage:
    python3 bench/fuzz_goals.py --seed 42 -n 1000 >> bench/goals.txt
"""

import argparse
import random

PROPS = ["p", "q", "r", "s"]
SETS = ["S", "T", "U"]
VARS = ["x", "y", "z", "w"]
EXPRS = ["a", "b", "c", "d"]


def rand_prop(rng, depth, max_depth):
    if depth >= max_depth:
        return rand_atom(rng)

    kind = rng.choices(
        ["atom", "not", "and", "or", "imp", "iff", "forall", "exists"],
        weights=[30, 10, 15, 10, 15, 5, 10, 5],
        k=1
    )[0]

    if kind == "atom":
        return rand_atom(rng)
    elif kind == "not":
        return f"not({rand_prop(rng, depth+1, max_depth)})"
    elif kind == "and":
        n = rng.choice([2, 3])
        parts = [rand_prop(rng, depth+1, max_depth) for _ in range(n)]
        return " and ".join(parts)
    elif kind == "or":
        n = rng.choice([2, 3])
        parts = [rand_prop(rng, depth+1, max_depth) for _ in range(n)]
        return " or ".join(parts)
    elif kind == "imp":
        a = rand_prop(rng, depth+1, max_depth)
        b = rand_prop(rng, depth+1, max_depth)
        return f"{a} => {b}"
    elif kind == "iff":
        a = rand_prop(rng, depth+1, max_depth)
        b = rand_prop(rng, depth+1, max_depth)
        return f"{a} <=> {b}"
    elif kind == "forall":
        v = rng.choice(VARS)
        body = rand_prop(rng, depth+1, max_depth)
        return f"!{v}.({body})"
    elif kind == "exists":
        v = rng.choice(VARS)
        body = rand_prop(rng, depth+1, max_depth)
        return f"#{v}.({body})"
    return rand_atom(rng)


def rand_atom(rng):
    kind = rng.choices(
        ["prop", "mem", "eq", "true", "false"],
        weights=[40, 25, 25, 5, 5],
        k=1
    )[0]

    if kind == "prop":
        return rng.choice(PROPS)
    elif kind == "mem":
        return f"{rng.choice(VARS + EXPRS)}: {rng.choice(SETS)}"
    elif kind == "eq":
        return f"{rng.choice(VARS + EXPRS)}={rng.choice(VARS + EXPRS)}"
    elif kind == "true":
        return "VRAI"
    elif kind == "false":
        return "FAUX"
    return rng.choice(PROPS)


def rand_goal(rng, max_depth=3):
    """Generate a random formula. No validity filtering."""
    kind = rng.choices(
        ["random", "imp_self", "lem", "imp_taut", "quant_taut",
         "contrapositive", "demorgan", "dist"],
        weights=[40, 5, 5, 15, 15, 5, 5, 10],
        k=1
    )[0]

    if kind == "random":
        return rand_prop(rng, 0, max_depth)
    elif kind == "imp_self":
        p = rand_prop(rng, 0, max_depth - 1)
        return f"({p} => {p})"
    elif kind == "lem":
        p = rand_prop(rng, 0, max_depth - 1)
        return f"({p} or not({p}))"
    elif kind == "imp_taut":
        p = rand_prop(rng, 0, max_depth - 1)
        q = rand_prop(rng, 0, max_depth - 1)
        return f"({p} => ({q} => {p}))"
    elif kind == "quant_taut":
        v = rng.choice(VARS)
        p = rand_prop(rng, 0, max_depth - 1)
        q = rand_prop(rng, 0, max_depth - 1)
        pattern = rng.choice([
            f"!{v}.({p} => {q}) => (!{v}.({p}) => !{v}.({q}))",
            f"!{v}.({p}) => {p}",
            f"{p} => #{v}.({p})",
            f"!{v}.({p} and {q}) => (!{v}.({p}) and !{v}.({q}))",
        ])
        return pattern
    elif kind == "contrapositive":
        p = rand_prop(rng, 0, max_depth - 1)
        q = rand_prop(rng, 0, max_depth - 1)
        return f"(({p} => {q}) => (not({q}) => not({p})))"
    elif kind == "demorgan":
        p = rand_prop(rng, 0, max_depth - 1)
        q = rand_prop(rng, 0, max_depth - 1)
        pattern = rng.choice([
            f"(not({p} and {q}) => (not({p}) or not({q})))",
            f"(not({p} or {q}) => (not({p}) and not({q})))",
            f"((not({p}) or not({q})) => not({p} and {q}))",
            f"((not({p}) and not({q})) => not({p} or {q}))",
        ])
        return pattern
    elif kind == "dist":
        p = rand_prop(rng, 0, max_depth - 2)
        q = rand_prop(rng, 0, max_depth - 2)
        r = rand_prop(rng, 0, max_depth - 2)
        return f"(({p} and ({q} or {r})) => (({p} and {q}) or ({p} and {r})))"
    return rand_prop(rng, 0, max_depth)


def main():
    parser = argparse.ArgumentParser(
        description="Generate random FOL goals in PP syntax"
    )
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("-n", "--count", type=int, default=1000)
    parser.add_argument("--max-depth", type=int, default=3)
    parser.add_argument("--prefix", default="fuzz")
    args = parser.parse_args()

    rng = random.Random(args.seed)
    seen = set()

    print(f"# Auto-generated goals (seed={args.seed}, n={args.count})")

    generated = 0
    attempts = 0
    while generated < args.count:
        attempts += 1
        if attempts > args.count * 10:
            break
        formula = rand_goal(rng, max_depth=args.max_depth)
        if formula in seen:
            continue
        seen.add(formula)
        name = f"{args.prefix}_{generated:04d}"
        print(f"{name:<25s} {formula}")
        generated += 1


if __name__ == "__main__":
    main()
