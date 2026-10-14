"""The real example of `box-perturbation.tex`: EU KLEMS 2023, United States, total economy,
1995-2020 (`data/us_tot.csv`, T = 26).

Prices P_t = (K_t / II_t, L_t / II_t) with K = (VA_CP - COMP) / Kq_GFCF, L = COMP / H_EMP,
II = II_CP / II_Q, each divided by its maximum over the years.  Output y = GO_Q.

The script finds the least maximal log deviation rho = max_{i,t} |ln q^i_t - ln p^i_t| over the 2T
prices at which y is weakly solvable: the least rho with BOX(P e^{-rho}, P e^{rho}, y), by
bisection on `box.decide`.  Both sides are certified exactly (NO: Farkas vector at
rho(1 - 1e-4), YES: rational witness at rho(1 + 1e-4)), and `example.png` is drawn.
Run from this folder: ../.venv/bin/python example.py
"""

import csv
import math
from fractions import Fraction as F
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Rectangle  # noqa: E402

import box  # noqa: E402

HERE = Path(__file__).resolve().parent
EPS = 1e-4


def load():
    """(P, y, years): prices (K/II, L/II) after dividing K, L, II by their maxima."""
    rows = list(csv.DictReader(open(HERE / "data" / "us_tot.csv")))
    v = [{k: F(x) for k, x in r.items()} for r in rows]
    P3 = [((r["VA_CP"] - r["COMP"]) / r["Kq_GFCF"], r["COMP"] / r["H_EMP"], r["II_CP"] / r["II_Q"])
          for r in v]
    mx = [max(p[i] for p in P3) for i in range(3)]
    P3 = [tuple(p[i] / mx[i] for i in range(3)) for p in P3]
    return [(p[0] / p[2], p[1] / p[2]) for p in P3], [r["GO_Q"] for r in v], [int(r["year"]) for r in rows]


def log_box(P, rho):
    """The box |ln q^i_t - ln p^i_t| <= rho with exact rational corners."""
    k = F(math.exp(rho)).limit_denominator(10**12)
    return [(a / k, b / k) for a, b in P], [(a * k, b * k) for a, b in P]


def least_radius(P, y, tol=1e-6):
    """Least rho with BOX(log_box(P, rho), y), by bisection."""
    lo, hi = 0.0, 1.0
    if box.decide(P, P, y):
        return 0.0
    while not box.decide(*log_box(P, hi), y):
        hi *= 2
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if box.decide(*log_box(P, mid), y):
            hi = mid
        else:
            lo = mid
    return hi


def main():
    P, y, years = load()
    rho = least_radius(P, y)
    below, above = log_box(P, rho * (1 - EPS)), log_box(P, rho * (1 + EPS))
    lam = box.refute(*below, y)
    Q, cert = box.witness(*above, y)
    assert lam is not None and box.in_box(Q, *above) and box.certify(Q, y, cert)
    print(f"T = {len(P)}, {years[0]}-{years[-1]}")
    print(f"least max |ln q - ln p| = {rho:.4f} (+-{100 * math.expm1(rho):.1f}%)")
    print(f"NO  at rho(1 - {EPS}): exact Farkas vector")
    print(f"YES at rho(1 + {EPS}): exact witness, {len(cert)} weakly reachable sets")

    L, U = above
    fig, ax = plt.subplots(figsize=(5.6, 4.8))
    for t in range(len(P)):
        ax.add_patch(Rectangle((float(L[t][0]), float(L[t][1])), float(U[t][0] - L[t][0]),
                               float(U[t][1] - L[t][1]), fill=False, ec="#bbbbbb", lw=0.6))
        ax.plot([float(P[t][0]), float(Q[t][0])], [float(P[t][1]), float(Q[t][1])], color="k", lw=0.5)
    sc = ax.scatter([float(p[0]) for p in P], [float(p[1]) for p in P], c=[float(v) for v in y],
                    cmap="viridis", s=24, label="observed $p_t$")
    ax.scatter([float(q[0]) for q in Q], [float(q[1]) for q in Q], marker="x", c="#cc3311", s=24,
               label="solution $q_t$")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set(xlabel="$p_K/p_{II}$", ylabel="$p_L/p_{II}$")
    ax.legend(loc="upper left", fontsize=8)
    fig.colorbar(sc, label="output $y_t$")
    fig.tight_layout()
    fig.savefig(HERE / "example.png", dpi=150)


if __name__ == "__main__":
    main()
