"""d = 3 breakpoint statistics for the US data (EU KLEMS, data/us_tot.csv, T = 26).

There is no output-price column; the nominal gross output is GO_CP = VA_CP + II_CP (accounting
identity), so the output price is GO_CP / GO_Q.  Prices (K, L, II) are each divided by their maximum
over the years, then by the output price (also divided by its maximum): d = 3, y = GO_Q.
The weak-solvability oracle for d = 3 is a black box (to be plugged in), so the search is run only
when T <= 4 with `proj.oracle_brute`; otherwise only the breakpoint statistics are printed.
Run from this folder: ../.venv/bin/python example_d3.py [T]
"""

import csv
import sys
from fractions import Fraction as F
from pathlib import Path

import proj

HERE = Path(__file__).resolve().parent


def load(T=None):
    rows = list(csv.DictReader(open(HERE / "data" / "us_tot.csv")))
    v = [{k: F(x) for k, x in r.items()} for r in rows]
    P4 = [((r["VA_CP"] - r["COMP"]) / r["Kq_GFCF"], r["COMP"] / r["H_EMP"], r["II_CP"] / r["II_Q"],
           (r["VA_CP"] + r["II_CP"]) / r["GO_Q"]) for r in v]
    mx = [max(p[i] for p in P4) for i in range(4)]
    P4 = [tuple(p[i] / mx[i] for i in range(4)) for p in P4]
    P = [(p[0] / p[3], p[1] / p[3], p[2] / p[3]) for p in P4]
    y = [r["GO_Q"] for r in v]
    return (P[:T], y[:T]) if T else (P, y)


def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else None
    P, y = load(T)
    print(f"d = 3, T = {len(P)}")
    roots, st = proj.breakpoints(P, return_stats=True)
    for k, v in st.items():
        print(f"  {k}: {v if not isinstance(v, float) else round(v, 2)}")
    if len(P) <= 4:
        res = proj.least_radius_exact(P, y, proj.oracle_brute, roots=roots)
        print(f"rho* = {res.rho:.6f}, calls = {res.n_calls}, gap = {res.gap}")
    else:
        print("search skipped: the d = 3 weak-solvability oracle is a black box (oracle_brute only for T <= 4)")


if __name__ == "__main__":
    main()
