"""Maximal weakly solvable year intervals of one industry at d = 2, 3, 8 (and the d = 8 placebo).

A year interval [a, b] is solvable if the outputs of these years are weakly solvable at the observed prices of
these years (one call of the exact oracle with lo = hi = y).  Solvability is preserved by deleting years, so the
solvable intervals are down-closed and the maximal ones are found by a two-pointer sweep in O(T) oracle calls:
for every start a the largest end b(a) is nondecreasing in a, and [a, b(a)] is maximal iff b(a) > b(a - 1).

Output: one json line per (kind, ind, d, seed) in --out with the maximal intervals (years) and their lengths;
`table` prints, per industry, the lengths at each d.  Uses the exact oracle (a MILP pricing), so one run at a time.

    nice -n 19 python experiments/intervals.py real 15 24 1
    nice -n 19 python experiments/intervals.py placebo 15:1 24:1
    python experiments/intervals.py table
"""

import argparse
import json
import time
from fractions import Fraction as F

from aggregation_lp import load
from figures import RESULTS
from neotiling.oracle import as_answer
from neotiling.oracle.exact import oracle_exact


def solvable(P, y, a, b):
    """Weak solvability of the years a..b (inclusive) at their own prices."""
    W = [tuple(F(c) for c in P[t]) for t in range(a, b + 1)]
    yy = [F(y[t]) for t in range(a, b + 1)]
    return as_answer(oracle_exact(W, yy, yy)).feasible


def maximal_intervals(P, y):
    """Maximal solvable intervals [a, b] as index pairs; a single year is always solvable."""
    T = len(P)
    out, b = [], -1
    for a in range(T):
        b = max(b, a)
        while b + 1 < T and solvable(P, y, a, b + 1):
            b += 1
        if not out or b > out[-1][1]:
            out.append((a, b))
    return out


def run(kind, ind, d, seed, args):
    P, y, years = load(kind, ind, d, seed, args.T)
    t0 = time.time()
    iv = maximal_intervals(P, y)
    row = {"kind": kind, "ind": ind, "d": d, "seed": seed, "T": len(P),
           "intervals": [[years[a], years[b]] for a, b in iv], "lengths": [b - a + 1 for a, b in iv],
           "time": time.time() - t0}
    print(f"BEA {ind:2d} d={d} {kind}{'' if seed is None else f' seed {seed}'}: lengths {row['lengths']} "
          f"{row['time']:.0f}s", flush=True)
    with open(args.out, "a") as f:
        f.write(json.dumps(row) + "\n")


def table(path):
    rows = {}
    for s in open(path):
        if s.strip():
            r = json.loads(s)
            rows[(r["kind"], r["ind"], r["d"], r.get("seed"))] = r      # the last run of a cell wins
    inds = sorted({k[1] for k in rows})
    seeds = sorted({k[3] for k in rows if k[0] == "placebo"})
    head = ["industry", "d=2", "d=3", "d=8"] + [f"placebo seed {s}" for s in seeds]
    print("| " + " | ".join(head) + " |\n|" + "---|" * len(head))
    fmt = lambda r: "-" if r is None else f"{max(r['lengths'])} / {len(r['lengths'])} / " + \
        " ".join(map(str, sorted(r["lengths"], reverse=True)))
    for ind in inds:
        cols = [fmt(rows.get(("real", ind, d, None))) for d in (2, 3, 8)]
        cols += [fmt(rows.get(("placebo", ind, 8, s))) for s in seeds]
        print(f"| {ind} | " + " | ".join(cols) + " |")
    print("\ncell = longest / number of maximal intervals / all lengths")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=["real", "placebo", "table"])
    ap.add_argument("items", nargs="*", help="IND (real) or IND:SEED (placebo)")
    ap.add_argument("--dims", default="2,3,8")
    ap.add_argument("--T", type=int, default=40)
    ap.add_argument("--out", default=str(RESULTS / "intervals.jsonl"))
    args = ap.parse_args()
    if args.mode == "table":
        return table(args.out)
    for a in args.items:
        if args.mode == "real":
            for d in map(int, args.dims.split(",")):
                run("real", int(a), d, None, args)
        else:
            i, s = a.split(":")
            run("placebo", int(i), 8, int(s), args)


if __name__ == "__main__":
    main()
