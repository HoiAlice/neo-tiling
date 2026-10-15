"""Unsolvability measure rho*/rho_bar on BEA industries at d = 3: prices (pK, pL, pII) / pGO from the
aggregate file, y = GO_Q, T = 40, weights K 1, L 3, II 3, GO 4 with the year factor; rho* by bisection
with the exact oracle (exact_oracle.oracle_exact).  rho_bar = min_i min_c max_t |ln c - ln p_t^i| / v_t^i
(cost of aligning one coordinate, an upper bound for rho*).  rho*/rho_bar = 1 means the least
perturbation is no better than the trivial one (the profile then collapsed onto p_i = const at d = 2).
Output: results/ratio_d3.log.  Run: nice -n 19 ../.venv/bin/python experiments/ratio_d3.py [industries]
"""

import csv
import sys
import time
from fractions import Fraction as F

import numpy as np

from _common import RESULTS
from perturb import zono
from perturb.data import DATA
from perturb.exact_oracle import oracle_exact

NAMES = ["K", "L", "II", "GO"]


def load_bea_d3(ind, T=40):
    with open(DATA / "bea_klems_1963_2016.csv") as f:
        rows = [r for r in csv.DictReader(f) if int(r["indnum"]) == ind]
    rs = sorted(rows, key=lambda r: int(r["year"]))[-T:]
    P = [tuple(F(r[c]) / F(r["pGO"]) for c in ("pK", "pL", "pII")) for r in rs]
    return P, [F(r["GO_Q"]) for r in rs], [int(r["year"]) for r in rs], rs[0]["industry"]


def rho_bar(P, kap, k0):
    """Per coordinate: min_c max_t |ln c - ln p_t^i| / v_t^i (bisection on the value)."""
    out = []
    for i in range(len(P[0])):
        x = np.array([np.log(float(p[i])) for p in P])
        v = np.array([zono.path_vector(kap[t], k0[t])[i] for t in range(len(P))])
        lo, hi = 0.0, 10.0
        for _ in range(100):
            m = (lo + hi) / 2
            if np.max(x - m * v) <= np.min(x + m * v):
                hi = m
            else:
                lo = m
        out.append(hi)
    return out


def main(inds):
    for ind in inds:
        P, y, years, name = load_bea_d3(ind)
        P = [tuple(float(c) for c in p) for p in P]
        kap, k0 = zono.default_weights(years, 3, NAMES)
        rb = rho_bar(P, kap, k0)
        i = int(np.argmin(rb))
        t0 = time.time()
        lo, hi, calls, _ = zono.least_wradius(P, y, kap, k0, oracle_exact, tol=1e-5)
        line = (f"BEA {ind:2d} {name[:28]:28s} d=3: rho* in [{lo:.5f}, {hi:.5f}], rho_bar {rb[i]:.5f} "
                f"({NAMES[i]}), ratio {hi / rb[i]:.3f}, {calls} calls, {time.time() - t0:.0f}s")
        print(line, flush=True)
        with open(RESULTS / "ratio_d3.log", "a") as f:
            f.write(line + "\n")


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]] or [15, 1, 6, 12, 24, 27, 31, 46, 49, 63])
