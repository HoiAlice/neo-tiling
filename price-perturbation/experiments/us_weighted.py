"""Weighted (zonotope) perturbation on the US data (d = 2): rho*, witness, picture.

Weights: zono.default_weights (K = 1, L = 3, II = 3, year factor 0.5 .. 1).  Left panel: those
weights; right panel: equal weights (all steps parallel to the diagonal).  Output:
tex/figures/example_zono.png.  Run: ../.venv/bin/python experiments/us_weighted.py
"""

import math
import time

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402
from scipy.spatial import ConvexHull  # noqa: E402

from _common import FIGURES  # noqa: E402
from perturb import proj, zono  # noqa: E402
from perturb.data import load_us_d2  # noqa: E402

NAMES = ["K", "L", "II"]


def flow(W, lo, hi):
    return proj.oracle_flow(W, lo, hi, certify=False)


def solve(P, y, years, kappa, kappa0):
    t0 = time.time()
    lo, hi, calls, ans = zono.least_wradius(P, y, kappa, kappa0, flow, tol=1e-6)
    t1 = time.time()
    a, inner = zono.solve_at(P, y, kappa, kappa0, hi, proj.oracle_flow)
    w = zono.wwitness(P, y, kappa, kappa0, hi, a.columns, a.masses, inner)
    print(f"rho* in [{lo:.6f}, {hi:.6f}], {calls} oracle calls, bisection {t1 - t0:.1f}s, "
          f"witness {time.time() - t1:.1f}s, witness check {w['feasible']}, max dist {w['maxdist']:.6f}")
    return hi, w


def zonotope(p, kappa_t, kappa0_t, rho):
    """Vertices (price space) of the ball {d_kappa <= rho} around p: log-box plus diagonal segment."""
    lp = np.log(np.array([float(c) for c in p]))
    A = [rho / k for k in kappa_t]
    c = rho / kappa0_t
    pts = [(sx * A[0] + sd * c, sy * A[1] + sd * c) for sx in (1, -1) for sy in (1, -1) for sd in (1, -1)]
    pts = np.array(pts)
    hull = pts[ConvexHull(pts).vertices]
    hull = np.vstack([hull, hull[:1]])
    return np.exp(lp + hull)


def panel(ax, P, y, years, kappa, kappa0, rho, w, title):
    for t, p in enumerate(P):
        z = zonotope(p, kappa[t], kappa0[t], rho)
        ax.plot(z[:, 0], z[:, 1], color="#bbbbbb", lw=0.6)
    for p, q in zip(P, w["Q"]):
        ax.plot([float(p[0]), q[0]], [float(p[1]), q[1]], color="k", lw=0.5)
    ax.scatter([float(p[0]) for p in P], [float(p[1]) for p in P], marker="x", c="#cc3311", s=22,
               label="observed $p_t$ (from)", zorder=3)
    sc = ax.scatter([q[0] for q in w["Q"]], [q[1] for q in w["Q"]], c=[float(v) for v in y],
                    cmap="viridis", s=24, label="solution $q_t$ (to)", zorder=4)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set(xlabel="$p_K/p_{II}$", ylabel="$p_L/p_{II}$", title=title)
    ax.legend(loc="upper left", fontsize=7)
    return sc


def main():
    P, y, years = load_us_d2()
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
    fig.savefig(FIGURES / "example_zono.png", dpi=150, bbox_inches="tight")
    label, kap, k0, rho, w = runs[0]
    print("weighted solution: year, d ln K, d ln L, d ln II (absolute, shift s = -theta/kappa0)")
    for t in range(T):
        th = w["theta"][t]
        print(f"  {years[t]}  {th / kap[t][0]:+.4f}  {th / kap[t][1]:+.4f}  {-th / k0[t]:+.4f}")


if __name__ == "__main__":
    main()
