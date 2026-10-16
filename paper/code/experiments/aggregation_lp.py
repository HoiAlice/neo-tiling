"""Does aggregation of prices inflate the least l_1 price perturbation OPT_1 (relative metric)?

BEA industries at d = 8 (five capital types, two labour types, II, all divided by pGO; y = GO_Q, T = 40),
d = 3 (K, L, II / GO) and d = 2 (K, L / II).  OPT_1 = UB of `neotiling.lp.solve` (LB <= OPT_1 <= UB).
Placebo (d = 8 only): for every capital / labour type the deviations ln p_{k,t} - ln p_{K,t} from its
aggregate (pK or pL of the aggregate file) are permuted over the years (seeded).  The size of the detail is
kept, its link to the years is destroyed.  Expected message: the real disaggregation lowers OPT_1 much more
than the placebo, so the drop is not the mechanical effect of more coordinates.
Output: one json line per run in --out.  One solver run at a time:
    nice -n 19 python experiments/aggregation_lp.py real 15 1 24
    nice -n 19 python experiments/aggregation_lp.py placebo 15:1 15:2 24:1
    python experiments/aggregation_lp.py table        (or --table): markdown table of UB, * = not optimal
"""

import argparse
import csv
import json
import math
import random
import time
from fractions import Fraction as F

from figures import RESULTS
from neotiling import data
from neotiling.data import CSV
from neotiling.lp.problem import Problem
from neotiling.lp.solve import solve

K = ["pKit", "pKsoft", "pKrd", "pKart", "pKoth"]
L = ["pLcol", "pLn"]


def load_d3(ind, T):
    with open(CSV / "bea_klems_1963_2016.csv") as f:
        rs = sorted((r for r in csv.DictReader(f) if int(r["indnum"]) == ind), key=lambda r: int(r["year"]))[-T:]
    P = [tuple(F(F(r[c]) / F(r["pGO"])).limit_denominator(10**9) for c in ("pK", "pL", "pII")) for r in rs]
    return P, [F(r["GO_Q"]) for r in rs], [int(r["year"]) for r in rs]


def load_placebo(ind, seed, T):
    with open(CSV / "bea_klems_detail_1963_2016.csv") as f:
        det = sorted((r for r in csv.DictReader(f) if int(r["indnum"]) == ind), key=lambda r: int(r["year"]))[-T:]
    with open(CSV / "bea_klems_1963_2016.csv") as f:
        agg = {int(r["year"]): r for r in csv.DictReader(f) if int(r["indnum"]) == ind}
    years = [int(r["year"]) for r in det]
    rnd = random.Random(seed)
    cols = []
    for group, ac in ((K, "pK"), (L, "pL")):
        for c in group:
            dev = [math.log(float(r[c])) - math.log(float(agg[y][ac])) for r, y in zip(det, years)]
            perm = list(range(len(det)))
            rnd.shuffle(perm)
            cols.append([math.exp(math.log(float(agg[y][ac])) + dev[perm[t]]) for t, y in enumerate(years)])
    cols.append([float(r["pII"]) for r in det])
    P = [tuple(F(col[t] / float(det[t]["pGO"])).limit_denominator(10**9) for col in cols) for t in range(len(det))]
    return P, [F(r["GO_Q"]) for r in det], years


def run(kind, ind, d, seed, args):
    if kind == "placebo":
        P, y, _ = load_placebo(ind, seed, args.T)
    elif d == 3:
        P, y, _ = load_d3(ind, args.T)
    else:
        P, y, _ = data.bea(ind, d, args.T)
    prob = Problem(P, y, p=args.p, metric="rel")
    t0 = time.time()
    res = solve(prob, eps=args.eps, time_limit=args.time_limit)
    Q = res.get("Q")
    n_moved = None if Q is None else sum(abs(float(q) / float(p) - 1) > 1e-5
                                         for Qt, Pt in zip(Q, P) for q, p in zip(Qt, Pt))
    row = {"kind": kind, "ind": ind, "d": d, "seed": seed, "T": args.T, "p": args.p, "metric": "rel",
           "LB": res["LB"], "UB": res["UB"], "status": res["status"], "time": time.time() - t0, "n_moved": n_moved}
    print(f"BEA {ind:2d} d={d} {kind}{'' if seed is None else f' seed {seed}'}: LB {res['LB']:.6f} "
          f"UB {res['UB']:.6f} {res['status']} moved {n_moved} {row['time']:.0f}s", flush=True)
    with open(args.out, "a") as f:
        f.write(json.dumps(row) + "\n")


def table(path):
    rows = [json.loads(s) for s in open(path) if s.strip()]
    fmt = lambda rs: "-" if not rs else f"{sum(r['UB'] for r in rs) / len(rs):.4f}" + (
        "*" if any(r["status"] != "optimal" for r in rs) else "")
    print("| industry | d=2 | d=3 | d=8 | placebo (mean) |\n|---|---|---|---|---|")
    for ind in sorted({r["ind"] for r in rows}):
        sel = lambda k, d: [r for r in rows if r["ind"] == ind and r["kind"] == k and r["d"] == d]
        print(f"| {ind} | {fmt(sel('real', 2))} | {fmt(sel('real', 3))} | {fmt(sel('real', 8))} | "
              f"{fmt(sel('placebo', 8))} |")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=["real", "placebo", "table"])
    ap.add_argument("items", nargs="*", help="IND (real) or IND:SEED (placebo)")
    ap.add_argument("--dims", default="2,3,8")
    ap.add_argument("--p", type=float, default=1.0)
    ap.add_argument("--eps", type=float, default=1e-4)
    ap.add_argument("--time-limit", type=float, default=600.0)
    ap.add_argument("--T", type=int, default=40)
    ap.add_argument("--out", default=str(RESULTS / "aggregation_lp.jsonl"))
    ap.add_argument("--table", action="store_true")
    args = ap.parse_args()
    if args.table or args.mode == "table":
        return table(args.out)
    for a in args.items:
        if args.mode == "real":
            for d in map(int, args.dims.split(",")):
                run("real", int(a), d, None, args)
        else:
            i, s = a.split(":")
            run("placebo", int(i), 8, int(s), args)    # the placebo only exists at full detail, d = 8


if __name__ == "__main__":
    main()
