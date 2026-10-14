"""Exact check of the upper-bound certificates in a results.jsonl of gurobi/rho_gurobi.py.

For each instance the sets and witnesses of the best certificate are taken as rationals,
the LP in Q is re-solved exactly (pycddlib, GMP rationals) and the certificate is verified
in Fractions. Prints the exact upper bound next to the reported LB and UB.

    python -m exact.check_results path/to/results.jsonl
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction

from . import certify as C


def check(rec):
    P = [[Fraction(v).limit_denominator(10**12) for v in row] for row in rec["P"]]
    y = [Fraction(v).limit_denominator(10**12) for v in rec["y"]]
    best = rec["best"]
    sets = [frozenset(S) for S in best["sets"]]
    wit = {}
    for key, xi in best["witness"].items():
        k, t = map(int, key.split(","))
        xi = [Fraction(v) for v in xi]
        wit[k, t] = [v / sum(xi) for v in xi]
    m = C.cone_masses(y, sets)
    if m is None:
        return None
    val, Q = C.best_prices(P, y, sets, wit)
    return C.verify(P, y, Q, sets, m, wit)


def main():
    for line in open(sys.argv[1]):
        rec = json.loads(line)
        name = rec.get("name", "?")
        exact = check(rec) if "best" in rec else None
        shown = f"{float(exact):.9f}" if exact is not None else "-"
        print(f"{name:22s} LB {rec.get('LB', float('nan')):.9f}  UB {rec.get('UB', float('nan')):.9f}"
              f"  exact UB {shown}  {rec.get('status')}  {rec.get('error', '')}")


if __name__ == "__main__":
    main()
