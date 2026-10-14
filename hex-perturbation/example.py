"""Real example: EU KLEMS 2023, United States, total economy, 1995-2020 (data/us_tot.csv, T = 26).

Prices P_t = (K_t / II_t, L_t / II_t) (each divided by its maximum over the years), output
y = GO_Q.  Computes the exact least hexagonal radius rho* (`hex.least_radius_exact`), certifies it
exactly and compares with the old float bisection value (box-perturbation, rho* ~ 0.0897).
Run from this folder: ../.venv/bin/python example.py
"""

import csv
import math
import time
from fractions import Fraction as F
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

import hex as hx  # noqa: E402

HERE = Path(__file__).resolve().parent
OLD_RHO = 0.0897


def load():
    """(P, y, years): prices (K/II, L/II) after dividing K, L, II by their maxima."""
    rows = list(csv.DictReader(open(HERE / "data" / "us_tot.csv")))
    v = [{k: F(x) for k, x in r.items()} for r in rows]
    P3 = [((r["VA_CP"] - r["COMP"]) / r["Kq_GFCF"], r["COMP"] / r["H_EMP"], r["II_CP"] / r["II_Q"])
          for r in v]
    mx = [max(p[i] for p in P3) for i in range(3)]
    P3 = [tuple(p[i] / mx[i] for i in range(3)) for p in P3]
    return [(p[0] / p[2], p[1] / p[2]) for p in P3], [r["GO_Q"] for r in v], [int(r["year"]) for r in rows]


def hexagon(p, rho):
    """Vertices (in the plane) of the hexagon {q : dhat(q, p) <= rho}, p = (p1, p2)."""
    l1, l2 = math.log(float(p[0])), math.log(float(p[1]))
    pts = [(rho, 0), (rho, rho), (0, rho), (-rho, 0), (-rho, -rho), (0, -rho)]
    return [(math.exp(l1 + a), math.exp(l2 + b)) for a, b in pts] + [
        (math.exp(l1 + pts[0][0]), math.exp(l2 + pts[0][1]))]


def main():
    P, y, years = load()
    t0 = time.time()
    roots = hx.breakpoints(P)
    t1 = time.time()
    res = hx.least_radius_exact(P, y, roots=roots)
    t2 = time.time()
    cert = hx.certify_result(P, y, res)
    t3 = time.time()
    print(f"T = {len(P)}, {years[0]}-{years[-1]}")
    print(f"rho* = {res.rho:.6f}   (old bisection: {OLD_RHO}, difference {abs(res.rho - OLD_RHO):.2e})")
    print(f"z* = e^(2 rho*) = {res.z_star.short(15)}  [{float(res.z_star):.12f}], "
          f"{'rational' if res.z_star.is_rational() else 'quadratic irrational'}")
    print(f"first feasible gap index = {res.gap}, k_below = {float(res.k_below):.10f}, "
          f"k_above = {float(res.k_above):.10f}")
    print(f"#breakpoints = {res.n_breakpoints}, #oracle calls = {res.n_calls}")
    print(f"NO  at k_below: exact Farkas vector: {cert['no_certified']}")
    print(f"YES at k_above: exact witness certified: {cert['yes_certified']}, "
          f"{cert.get('n_sets')} weakly reachable sets, witness in hexagons: {cert['witness_in_hex']}")
    print(f"notes: {res.notes}")
    print(f"time: breakpoints {t1 - t0:.1f}s, search {t2 - t1:.1f}s, certificates {t3 - t2:.1f}s")

    Q = cert["Q"]
    rho_a = cert["rho_above"]
    fig, ax = plt.subplots(figsize=(5.8, 4.8))
    for p in P:
        h = hexagon(p, rho_a)
        ax.plot([a for a, _ in h], [b for _, b in h], color="#bbbbbb", lw=0.6)
    for p, q in zip(P, Q):
        ax.plot([float(p[0]), float(q[0])], [float(p[1]), float(q[1])], color="k", lw=0.5)
    sc = ax.scatter([float(p[0]) for p in P], [float(p[1]) for p in P], c=[float(v) for v in y],
                    cmap="viridis", s=24, label="observed $p_t$")
    ax.scatter([float(q[0]) for q in Q], [float(q[1]) for q in Q], marker="x", c="#cc3311", s=24,
               label="solution $q_t$")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set(xlabel="$p_K/p_{II}$", ylabel="$p_L/p_{II}$",
           title=f"hexagons of radius $\\rho$ = {rho_a:.4f}")
    ax.legend(loc="upper left", fontsize=8)
    fig.colorbar(sc, label="output $y_t$")
    fig.tight_layout()
    fig.savefig(HERE / "example.png", dpi=150)


if __name__ == "__main__":
    main()
