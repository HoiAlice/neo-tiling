"""Exact least l_p price perturbation on data slices (the table of l1-perturbation/RESULTS.md).

For every slice, runs the polyblock / MILP algorithm of `neotiling.lp.solve` and prints LB, UB, status
and time; appends one json line per run to --out.

Slices (positional): us2, us3, bea:<ind>[:<d>[:<T>]] (d = 2, 4, 7, 8; default d = 8, T = 40),
va:<geo>:<industry> (EU KLEMS value-added model, d = 2), bw (Berndt-Wood, d = 4).

Example (one solver run at a time; nice for long runs):
    nice -n 19 python experiments/lp_runs.py us3 bea:15 va:US:M-N --p 1 --metric rel --eps 1e-4 \
        --time-limit 600 --out results/lp_runs.jsonl
"""

import argparse
import json
import math
import time

from figures import RESULTS
from neotiling import data
from neotiling.lp.problem import Problem
from neotiling.lp.solve import solve


def load(spec):
    parts = spec.split(":")
    kind = parts[0]
    if kind == "us2":
        return data.us_d2()
    if kind == "us3":
        return data.us_d3()
    if kind == "bw":
        return data.berndt_wood()
    if kind == "bea":
        ind = int(parts[1])
        d = int(parts[2]) if len(parts) > 2 else 8
        T = int(parts[3]) if len(parts) > 3 else 40
        return data.bea(ind, d, T)
    if kind == "va":
        return data.va_model(parts[1], parts[2])
    raise SystemExit(f"unknown slice {spec!r}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("slices", nargs="+")
    ap.add_argument("--p", type=float, default=1.0, help="norm exponent, 1 <= p <= inf (default 1)")
    ap.add_argument("--metric", choices=["rel", "log"], default="rel")
    ap.add_argument("--eps", type=float, default=1e-4, help="relative gap UB - LB <= eps UB")
    ap.add_argument("--time-limit", type=float, default=600.0, help="seconds per slice")
    ap.add_argument("--out", default=str(RESULTS / "lp_runs.jsonl"))
    args = ap.parse_args()
    for spec in args.slices:
        P, y, years = load(spec)
        if not P:
            print(f"{spec}: empty slice (broken series)", flush=True)
            continue
        prob = Problem(P, y, p=args.p, metric=args.metric)
        t0 = time.time()
        res = solve(prob, eps=args.eps, time_limit=args.time_limit)
        row = {"slice": spec, "d": prob.d, "T": prob.T, "p": args.p, "metric": args.metric, "eps": args.eps,
               "time_limit": args.time_limit, "LB": res["LB"], "UB": res["UB"], "status": res["status"],
               "time": time.time() - t0}
        print(f"{spec:16s} d={prob.d} T={prob.T}  LB {res['LB']:.6f}  UB {res['UB']:.6f}  {res['status']}  "
              f"{row['time']:.0f}s", flush=True)
        with open(args.out, "a") as f:
            f.write(json.dumps(row) + "\n")


if __name__ == "__main__":
    main()
