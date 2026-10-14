"""Lexicographic profile on the US data (d = 2), weights zono.default_weights.

Left: the old witness at rho* (zono.wwitness, all years move).  Right: the profile witness
(per-year radii r_t, minimal shifts: years not needing a correction stay at p_t).
Output: tex/figures/example_profile.png and the profile table.  Run:
nice -n 19 ../.venv/bin/python experiments/us_profile.py
"""

import time
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

from _common import FIGURES  # noqa: E402
from perturb import lexprofile as pr  # noqa: E402
from perturb import proj, zono  # noqa: E402
from perturb.data import load_us_d2  # noqa: E402
from us_weighted import NAMES, flow, panel, zonotope  # noqa: E402


def main():
    P, y, years = load_us_d2()
    P = [tuple(float(c) for c in p) for p in P]
    T = len(P)
    kap, k0 = zono.default_weights(years, 2, NAMES)

    t0 = time.time()
    lo, rho, calls0, _ = zono.least_wradius(P, y, kap, k0, flow, tol=1e-6)
    a, inner = zono.solve_at(P, y, kap, k0, rho, proj.oracle_flow)
    w_old = zono.wwitness(P, y, kap, k0, rho, a.columns, a.masses, inner)
    t1 = time.time()
    out = pr.profile(P, y, kap, k0, flow, tol=1e-6, witness=True, witness_oracle=proj.oracle_flow)
    t2 = time.time()
    r = out["r"]
    stage_of = {}
    for k, s in enumerate(out["stages"]):
        for t in s["years"]:
            stage_of[t] = k + 1
    nz = sum(1 for x in r if x == 0.0)
    st1 = len(out["stages"][0]["years"])
    print(f"rho* = {rho:.6f} ({calls0} calls, old witness {t1 - t0:.1f}s)")
    print(f"profile: {len(out['stages'])} stages, {st1} years fixed at stage 1, {nz} years with r_t = 0, "
          f"{out['calls']} oracle calls, {t2 - t1:.1f}s, branching at stages {out['meet_violated_at_stage']}, "
          f"witness BOX check {out.get('wfeasible')}, max d/r {out.get('maxratio', float('nan')):.6f}")
    print("year  r_t        theta_t     stage")
    for t in range(T):
        th = out["theta"][t] if out.get("theta") else float("nan")
        print(f"{years[t]}  {r[t]:.6f}  {th:+.6f}  {stage_of[t]}")

    fig, axs = plt.subplots(1, 2, figsize=(13, 5), sharex=True, sharey=True)
    sc = panel(axs[0], P, y, years, kap, k0, rho, w_old, f"witness at $\\rho^*$ = {rho:.4f}")
    ax = axs[1]
    for t, p in enumerate(P):
        if r[t] > 0:
            z = zonotope(p, kap[t], k0[t], r[t])
            ax.plot(z[:, 0], z[:, 1], color="#bbbbbb", lw=0.6)
    Q = out["Q"]
    for p, q in zip(P, Q):
        ax.plot([p[0], q[0]], [p[1], q[1]], color="k", lw=0.5)
    ax.scatter([p[0] for p in P], [p[1] for p in P], marker="x", c="#cc3311", s=22,
               label="observed $p_t$ (from)", zorder=3)
    ax.scatter([q[0] for q in Q], [q[1] for q in Q], c=[float(v) for v in y], cmap="viridis", s=24,
               label="solution $q_t$ (to)", zorder=4)
    moved = [t for t in range(T) if out["theta"][t] != 0.0]
    for t in sorted(range(T), key=lambda t: -r[t])[:5]:
        if r[t] > 0:
            ax.annotate(f"{years[t]}: {r[t]:.3f}", (P[t][0], P[t][1]), fontsize=7,
                        xytext=(4, 4), textcoords="offset points")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set(xlabel="$p_K/p_{II}$", title=f"lexicographic profile: {len(moved)} of {T} years moved")
    ax.legend(loc="upper left", fontsize=7)
    axs[0].set_ylabel("$p_L/p_{II}$")
    fig.colorbar(sc, ax=axs, label="output $y_t$")
    fig.savefig(FIGURES / "example_profile.png", dpi=150, bbox_inches="tight")


if __name__ == "__main__":
    main()
