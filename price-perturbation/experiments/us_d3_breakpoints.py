"""d = 3 breakpoint statistics for the US data (EU KLEMS, data/us_tot.csv, T = 26).

There is no output-price column; the nominal gross output is GO_CP = VA_CP + II_CP (accounting
identity), so the output price is GO_CP / GO_Q.  Prices (K, L, II) are each divided by their maximum
over the years, then by the output price (also divided by its maximum): d = 3, y = GO_Q.
The weak-solvability oracle for d = 3 is a black box (to be plugged in), so the search is run only
when T <= 4 with `proj.oracle_brute`; otherwise only the breakpoint statistics are printed.
Run: ../.venv/bin/python experiments/us_d3_breakpoints.py [T]
"""

import sys

import _common  # noqa: F401
from perturb import proj
from perturb.data import load_us_d3


def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else None
    P, y, _ = load_us_d3(T)
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
