"""Weighted (zonotope) perturbation on the US data (d = 2): rho*, witness, picture.

Weights: zono.default_weights (K = 1, L = 3, II = 3, year factor 0.5 .. 1).  Left panel: those
weights; right panel: equal weights (all steps parallel to the diagonal).  Output:
experiments/results/example_zono.png.  Run: python experiments/us_weighted.py
"""

import math
import time

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

from figures import RESULTS, panel  # noqa: E402
from neotiling.data import us_d2  # noqa: E402
from neotiling.oracle.flow_d2 import oracle_flow  # noqa: E402
from neotiling.radius import weighted as zono  # noqa: E402

NAMES = ["K", "L", "II"]


def flow(W, lo, hi):
    return oracle_flow(W, lo, hi, certify=False)


def solve(P, y, years, kappa, kappa0):
    t0 = time.time()
    lo, hi, calls, ans = zono.least_wradius(P, y, kappa, kappa0, flow, tol=1e-6)
    t1 = time.time()
    a, inner = zono.solve_at(P, y, kappa, kappa0, hi, oracle_flow)
    w = zono.wwitness(P, y, kappa, kappa0, hi, a.columns, a.masses, inner)
    print(f"rho* in [{lo:.6f}, {hi:.6f}], {calls} oracle calls, bisection {t1 - t0:.1f}s, "
          f"witness {time.time() - t1:.1f}s, witness check {w['feasible']}, max dist {w['maxdist']:.6f}")
    return hi, w


def main():
    P, y, years = us_d2()
    P = [tuple(float(c) for c in p) for p in P]
    T = len(P)
    runs = []
    kw, k0w = zono.default_weights(years, 2, NAMES)
    ke, k0e = zono.default_weights(years, 2, NAMES, base={"K": 1, "L": 1, "II": 1}, year_factor=False)
    for label, (kap, k0) in (("weighted", (kw, k0w)), ("equal weights", (ke, k0e))):
        print(label)
        rho, w = solve(P, y, years, kap, k0)
        runs.append((label, kap, k0, rho, w))
    fig, axs = plt.subplots(1, 2, figsize=(12, 4.8), sharex=True, sharey=True)
    for ax, (label, kap, k0, rho, w) in zip(axs, runs):
        sc = panel(ax, P, y, years, kap, k0, rho, w, f"{label}: $\\rho^*$ = {rho:.4f}")
    fig.colorbar(sc, ax=axs, label="output $y_t$")
    fig.savefig(RESULTS / "example_zono.png", dpi=150, bbox_inches="tight")
    label, kap, k0, rho, w = runs[0]
    print("weighted solution: year, d ln K, d ln L, d ln II (absolute, shift s = -theta/kappa0)")
    for t in range(T):
        th = w["theta"][t]
        print(f"  {years[t]}  {th / kap[t][0]:+.4f}  {th / kap[t][1]:+.4f}  {-th / k0[t]:+.4f}")


if __name__ == "__main__":
    main()
