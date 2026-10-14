"""US example (d = 2, T = 26): lexicographic profile of pair half-widths a_{t,i} (no weights).

Output: tex/figures/example_pairs.png.  Run: ../.venv/bin/python experiments/us_pairs.py
"""
import math
import time
from fractions import Fraction as F

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Rectangle  # noqa: E402

from _common import FIGURES  # noqa: E402
from perturb import box  # noqa: E402
from perturb import pairs as walls  # noqa: E402
from perturb.data import load_us_d2  # noqa: E402


def panel(ax, P, y, L, U, Q, title):
    for t in range(len(P)):
        x0, y0, x1, y1 = (float(L[t][0]), float(L[t][1]), float(U[t][0]), float(U[t][1]))
        ax.add_patch(Rectangle((x0, y0), x1 - x0, y1 - y0, fill=False, ec="#999999", lw=0.5))
        ax.plot([float(P[t][0]), float(Q[t][0])], [float(P[t][1]), float(Q[t][1])], color="k", lw=0.5)
    ax.scatter([float(p[0]) for p in P], [float(p[1]) for p in P], marker="x", c="#cc3311", s=28,
               label="observed (from)", zorder=3)
    sc = ax.scatter([float(q[0]) for q in Q], [float(q[1]) for q in Q], c=[float(v) for v in y],
                    cmap="viridis", s=18, label="solution (to)", zorder=4)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set(xlabel="$p_K/p_{II}$", ylabel="$p_L/p_{II}$", title=title)
    ax.legend(loc="upper left", fontsize=8)
    return sc


def main():
    P, y, years = load_us_d2()
    T = len(P)
    t0 = time.time()
    res = walls.wall_profile(P, y)
    dt = time.time() - t0
    lam, st = res["lam"], res["stages"]
    rho1 = st[0]["rho"]
    print(f"T = {T}, {years[0]}-{years[-1]}  (unit = pair (t, i), no weights)")
    print(f"rho* (stage 1) = {rho1:.6f}")
    print(f"#stages = {len(st)}, #pairs fixed per stage = {[s['B'] for s in st]}")
    print(f"stage levels = {[round(s['rho'], 6) for s in st]}")
    print(f"#oracle calls = {res['calls']}, time = {dt:.1f}s, branched = {res['branched']}")
    n0 = sum(1 for v in lam.values() if v <= 1e-12)
    print(f"pairs at level 0: {n0} of {2 * T}")

    # comparison: plain box at half-width rho1 in every coordinate
    a1 = [[rho1] * 2 for _ in range(T)]
    print("box at common level rho1 feasible:", walls.box_feasible(P, y, a1, a1))
    print("final box feasible:", walls.box_feasible(P, y, res["a_minus"], res["a_plus"]))

    Q = res["Q"]
    L, U = res["box"]
    print(f"\n{'year':>5} {'a_K':>9} {'a_L':>9} {'step_K':>9} {'step_L':>9}")
    for t in range(T):
        sK = math.log(float(Q[t][0]) / float(P[t][0]))
        sL = math.log(float(Q[t][1]) / float(P[t][1]))
        print(f"{years[t]:>5} {lam[(t, 0)]:9.5f} {lam[(t, 1)]:9.5f} {sK:+9.5f} {sL:+9.5f}")

    # stage-1 box with its exact witness
    Lc, Uc = walls.box_corners(P, a1, a1, True)
    rc = box.witness(Lc, Uc, [F(v) for v in y])
    Qc = rc[0]

    fig, axs = plt.subplots(1, 2, figsize=(12, 5))
    sc = panel(axs[0], P, y, L, U, Q, "lexicographic profile (final boxes)")
    panel(axs[1], P, y, Lc, Uc, Qc, f"common half-width $\\rho$ = {rho1:.4f}")
    fig.colorbar(sc, ax=axs, label="output $y_t$")
    fig.savefig(FIGURES / "example_pairs.png", dpi=150)

    # collapse diagnostics: log-log slope of solution points
    import numpy as np
    xs = np.log([float(q[0]) for q in Q])
    ys = np.log([float(q[1]) for q in Q])
    print("\ncorr(log qK, log qL) solution:", float(np.corrcoef(xs, ys)[0, 1]))
    xo = np.log([float(p[0]) for p in P])
    yo = np.log([float(p[1]) for p in P])
    print("corr(log pK, log pL) observed:", float(np.corrcoef(xo, yo)[0, 1]))
    print("max step K, L:", max(abs(math.log(float(Q[t][0]) / float(P[t][0]))) for t in range(T)),
          max(abs(math.log(float(Q[t][1]) / float(P[t][1]))) for t in range(T)))


if __name__ == "__main__":
    main()
