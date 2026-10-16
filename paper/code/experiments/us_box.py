"""Real example: EU KLEMS 2023, United States, total economy, 1995-2020 (neotiling/data/csv/us_tot.csv, T = 26).

Prices P_t = (K_t / II_t, L_t / II_t) (each divided by its maximum over the years), output
y = GO_Q.  Computes the exact least hexagonal radius rho* (`least_radius_exact` with the flow
oracle at d = 2, rational breakpoints of `reach.breakpoints`), certifies the YES side exactly
(`witness`) and compares with the old float bisection value (box-perturbation, rho* ~ 0.0897).
Output: experiments/results/example.png.  Run: python experiments/us_box.py
"""

import math
import time

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

from figures import RESULTS, hexagon  # noqa: E402
from neotiling.data import us_d2  # noqa: E402
from neotiling.geometry import reach  # noqa: E402
from neotiling.oracle.flow_d2 import oracle_flow  # noqa: E402
from neotiling.radius.least import least_radius_exact, witness  # noqa: E402

OLD_RHO = 0.0897


def main():
    P, y, years = us_d2()
    t0 = time.time()
    roots = reach.breakpoints(P)
    t1 = time.time()
    res = least_radius_exact(P, y, oracle_flow, roots=roots)
    t2 = time.time()
    ans = res.ans_above
    Q, cert, checks = witness(P, y, res.k_above, ans.columns, ans.masses)
    t3 = time.time()
    print(f"T = {len(P)}, {years[0]}-{years[-1]}")
    print(f"rho* = {res.rho:.6f}   (old bisection: {OLD_RHO}, difference {abs(res.rho - OLD_RHO):.2e})")
    print(f"z* = e^(2 rho*) = {res.z_star}  [{float(res.z_star):.12f}]")
    print(f"first feasible gap index = {res.gap}, k_below = {float(res.k_below):.10f}, "
          f"k_above = {float(res.k_above):.10f}")
    print(f"#breakpoints = {res.n_breakpoints}, #oracle calls = {res.n_calls}")
    print(f"YES at k_above: exact witness checks: {checks}, {len(cert)} weakly reachable sets")
    print(f"notes: {res.notes}")
    print(f"time: breakpoints {t1 - t0:.1f}s, search {t2 - t1:.1f}s, witness {t3 - t2:.1f}s")

    rho_a = math.log(float(res.k_above))
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
    fig.savefig(RESULTS / "example.png", dpi=150)


if __name__ == "__main__":
    main()
