"""Does aggregation of prices inflate the least l_1 price perturbation OPT_1 (relative metric)?

BEA industries at d = 8 (five capital types, two labour types, II, all divided by pGO; y = GO_Q, T = 40),
d = 3 (K, L, II / GO) and d = 2 (K, L / II).  OPT_1 = UB of `neotiling.lp.solve` (LB <= OPT_1 <= UB).
Placebo (d = 8 only): for every capital / labour type the deviations ln p_{k,t} - ln p_{K,t} from its
aggregate (pK or pL of the aggregate file) are permuted over the years (seeded).  The size of the detail is
kept, its link to the years is destroyed.  Expected message: the real disaggregation lowers OPT_1 much more
than the placebo, so the drop is not the mechanical effect of more coordinates.
Output: one json line per run in --out, with the solution Q and the list of moved coordinates (year, coord,
eps).  One solver run at a time (see aggregation_queue.sh):
    nice -n 19 python experiments/aggregation_lp.py real 15 1 24
    nice -n 19 python experiments/aggregation_lp.py real 15 --dims 2,3 --time-limit 1800
    nice -n 19 python experiments/aggregation_lp.py placebo 15:1 15:2 24:1
    python experiments/aggregation_lp.py table   markdown table: OPT_1 if optimal, else [LB, UB]; best run per cell
    python experiments/aggregation_lp.py moves   which coordinates the solutions move, per cell
Controls for "the correction sits on pII":
    nice -n 19 python experiments/aggregation_lp.py wii 24 1 27     d = 8, moving pII costs --w-ii (default 100)
    nice -n 19 python experiments/aggregation_lp.py d7go 24 1 27    the seven detailed prices / pGO, no pII coordinate
Logging (neotiling.logs): progress on stderr in real time and per run in results/logs/aggregation/<date>/;
-v adds the oracle's subproblems.
"""

import argparse
import csv
import json
import math
import random
import time
from fractions import Fraction as F

from figures import RESULTS
from neotiling import data, logs
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


def coord_names(d):
    """Names of the price coordinates of a slice (same order as the loaders)."""
    if d == 2:
        return ["pK/pII", "pL/pII"]
    if d == 3:
        return ["pK", "pL", "pII"]
    if d == 7:
        return K + L                 # the seven types divided by pII
    return K + L + ["pII"]


def load_d7go(ind, T):
    """Control: the seven detailed prices divided by pGO, no pII coordinate (data.bea(ind, 7) divides by pII)."""
    with open(CSV / "bea_klems_detail_1963_2016.csv") as f:
        rs = sorted((r for r in csv.DictReader(f) if int(r["indnum"]) == ind), key=lambda r: int(r["year"]))[-T:]
    P = [tuple(F(F(r[c]) / F(r["pGO"])).limit_denominator(10**9) for c in K + L) for r in rs]
    return P, [F(r["GO_Q"]) for r in rs], [int(r["year"]) for r in rs]


def load(kind, ind, d, seed, T):
    if kind == "placebo":
        return load_placebo(ind, seed, T)
    if kind == "d7go":
        return load_d7go(ind, T)
    if d == 3:
        return load_d3(ind, T)
    return data.bea(ind, d, T)


def weights(kind, d, T, w_ii):
    """Weights c (T x d): 1 everywhere, except kind "wii", where moving pII costs w_ii."""
    if kind != "wii":
        return None
    return [[w_ii if i == d - 1 else 1.0 for i in range(d)] for _ in range(T)]


def run(kind, ind, d, seed, args):
    P, y, years = load(kind, ind, d, seed, args.T)
    prob = Problem(P, y, c=weights(kind, d, len(P), args.w_ii), p=args.p, metric="rel")
    t0 = time.time()
    name = f"bea{ind}_d{d}_{kind}" + ("" if seed is None else f"_seed{seed}")
    with logs.run_file(logs.run_path(RESULTS, "aggregation", name)) as logfile:
        res = solve(prob, eps=args.eps, time_limit=args.time_limit)
    Q = res.get("Q")
    names = coord_names(d)
    moves = None if Q is None else [
        {"year": years[t], "coord": names[i], "eps": float(Q[t][i]) / float(P[t][i]) - 1}
        for t in range(len(P)) for i in range(d) if abs(float(Q[t][i]) / float(P[t][i]) - 1) > 1e-5]
    row = {"kind": kind, "ind": ind, "d": d, "seed": seed, "T": args.T, "p": args.p, "metric": "rel",
           "LB": res["LB"], "UB": res["UB"], "status": res["status"], "time": time.time() - t0,
           "time_limit": args.time_limit, "w_ii": args.w_ii if kind == "wii" else None,
           "n_moved": None if moves is None else len(moves), "moves": moves,
           "Q": None if Q is None else [[float(v) for v in Qt] for Qt in Q], "log": logfile}
    print(f"BEA {ind:2d} d={d} {kind}{'' if seed is None else f' seed {seed}'}: LB {res['LB']:.6f} "
          f"UB {res['UB']:.6f} {res['status']} moved {row['n_moved']} {row['time']:.0f}s", flush=True)
    with open(args.out, "a") as f:
        f.write(json.dumps(row) + "\n")


def _gap(r):
    """Sort key of a run of one cell: relative gap, then prefer runs that saved the solution."""
    gap = 0.0 if r["status"] == "optimal" else (r["UB"] - r["LB"]) / r["UB"] if r["UB"] > 0 else 1.0
    return (gap, 0 if r.get("Q") is not None else 1)


def best(rows):
    """One row per cell (kind, ind, d, seed): the optimal one, else the one with the smallest gap."""
    cells = {}
    for r in rows:
        k = (r["kind"], r["ind"], r["d"], r.get("seed"))
        if k not in cells or _gap(r) < _gap(cells[k]):
            cells[k] = r
    return cells


def _cell(r):
    if r is None:
        return "-"
    if r["status"] == "optimal":
        return f"{r['UB']:.4f}"
    return f"[{r['LB']:.3f}, {r['UB']:.3f}]"


def table(path):
    """Markdown table of OPT_1 (optimal) or [LB, UB] (time limit) per cell; the placebo seeds separately.
    A time-limited UB equal to the UB of another cell is the trivial bound of the alignment lemma."""
    cells = best([json.loads(s) for s in open(path) if s.strip()])
    inds = sorted({k[1] for k in cells})
    seeds = sorted({k[3] for k in cells if k[0] == "placebo"})
    cols = [(f"d={d}", ("real", d, None)) for d in (2, 3, 8) if any(k[:1] + k[2:3] == ("real", d) for k in cells)]
    if any(k[0] == "wii" for k in cells):
        cols.append(("d=8, pII weight", ("wii", 8, None)))
    if any(k[0] == "d7go" for k in cells):
        cols.append(("d=7 (/pGO, no pII)", ("d7go", 7, None)))
    cols += [(f"placebo d=8 seed {s}", ("placebo", 8, s)) for s in seeds]
    head = ["industry"] + [c[0] for c in cols]
    print("| " + " | ".join(head) + " |\n|" + "---|" * len(head))
    for ind in inds:
        print(f"| {ind} | " + " | ".join(_cell(cells.get((k, ind, d, s))) for _, (k, d, s) in cols) + " |")


def moves_table(path):
    """Which coordinates the optimal solutions move, per cell: count and total |eps| by coordinate group."""
    cells = best([json.loads(s) for s in open(path) if s.strip()])
    print("| cell | status | moved | by coordinate (count, sum |eps|) | years |\n|---|---|---|---|---|")
    for k in sorted(cells, key=lambda k: (k[1], k[0], k[2], k[3] or 0)):
        r = cells[k]
        if not r.get("moves"):
            continue
        by = {}
        for m in r["moves"]:
            c, s = by.get(m["coord"], (0, 0.0))
            by[m["coord"]] = (c + 1, s + abs(m["eps"]))
        desc = ", ".join(f"{c}: {n}, {s:.3f}" for c, (n, s) in sorted(by.items(), key=lambda x: -x[1][1]))
        yrs = ", ".join(str(y) for y in sorted({m["year"] for m in r["moves"]}))
        tag = f"{k[0]} {k[1]} d={k[2]}" + (f" seed {k[3]}" if k[3] is not None else "")
        print(f"| {tag} | {r['status']} | {r['n_moved']} | {desc} | {yrs} |")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=["real", "placebo", "wii", "d7go", "table", "moves"])
    ap.add_argument("items", nargs="*", help="IND (real) or IND:SEED (placebo)")
    ap.add_argument("--dims", default="2,3,8")
    ap.add_argument("--p", type=float, default=1.0)
    ap.add_argument("--eps", type=float, default=1e-4)
    ap.add_argument("--time-limit", type=float, default=600.0)
    ap.add_argument("--T", type=int, default=40)
    ap.add_argument("--w-ii", type=float, default=100.0, help="weight of moving pII in mode wii (d = 8)")
    ap.add_argument("--out", default=str(RESULTS / "aggregation_lp.jsonl"))
    ap.add_argument("--table", action="store_true")
    ap.add_argument("-v", "--verbose", action="store_true", help="log the oracle's subproblems too")
    args = ap.parse_args()
    if args.table or args.mode == "table":
        return table(args.out)
    if args.mode == "moves":
        return moves_table(args.out)
    logs.setup(verbose=args.verbose)
    for a in args.items:
        if args.mode == "real":
            for d in map(int, args.dims.split(",")):
                run("real", int(a), d, None, args)
        elif args.mode == "wii":
            run("wii", int(a), 8, None, args)
        elif args.mode == "d7go":
            run("d7go", int(a), 7, None, args)
        else:
            i, s = a.split(":")
            run("placebo", int(i), 8, int(s), args)    # the placebo only exists at full detail, d = 8


if __name__ == "__main__":
    main()
