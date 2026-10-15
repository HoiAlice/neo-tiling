"""One-sided lexicographic profile on the US data (d = 2), weights zono.default_weights.

Runs onesided.profile twice (default and reversed tie-break priority) and compares the results.
Output: tex/figures/example_onesided.png and the profile table.  Run:
nice -n 19 ../.venv/bin/python experiments/us_onesided.py [years to drop]
With years to drop (e.g. 2008 2020): weights of the full data, one run only, figure
example_onesided_no2008_no2020.png.
"""

import sys
import time

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

from _common import FIGURES  # noqa: E402
from perturb import onesided  # noqa: E402
from perturb import zono  # noqa: E402
from perturb.data import load_us_d2  # noqa: E402
from us_weighted import NAMES, flow  # noqa: E402


def main(drop=()):
    P, y, years = load_us_d2()
    P = [tuple(float(c) for c in p) for p in P]
    kap, k0 = zono.default_weights(years, 2, NAMES)       # weights of the full data, then drop
    keep = [t for t in range(len(P)) if years[t] not in drop]
    P, y, years = [P[t] for t in keep], [y[t] for t in keep], [years[t] for t in keep]
    kap, k0 = [kap[t] for t in keep], [k0[t] for t in keep]
    T = len(P)

    t0 = time.time()
    out = onesided.profile(P, y, kap, k0, flow, tol=1e-6)
    t1 = time.time()
    moved = [t for t in range(T) if out["theta"][t] != 0.0]
    print(f"one-sided profile: {len(out['stages'])} stages, {out['calls']} oracle calls, {t1 - t0:.1f}s, "
          f"ties {out['ties']}, verified {out['verified']}, tight {out['tight']}, both {out['both']}")
    if not drop:
        rev = onesided.profile(P, y, kap, k0, flow, tol=1e-6,
                               order=list(reversed(onesided.units(T))), check=False)
        diff = max(abs(a - b) for a, b in zip(out["theta"], rev["theta"]))
        print(f"reversed priority: {rev['calls']} calls, {time.time() - t1:.1f}s, ties {rev['ties']}, "
              f"max |theta - theta_rev| = {diff:.2e}")
    print(f"{len(moved)} of {T} years moved, max |theta| = {max(abs(x) for x in out['theta']):.6f}")
    stage_of = {}
    for k, s in enumerate(out["stages"]):
        for u in s["units"]:
            stage_of[u] = k + 1
    print("year  theta_t     stage")
    for t in range(T):
        th = out["theta"][t]
        u = (t, 1) if th > 0 else (t, -1)
        print(f"{years[t]}  {th:+.6f}  {stage_of[u] if th != 0 else '-'}")

    fig, ax = plt.subplots(figsize=(7, 5))
    Q = out["Q"]
    for p, q in zip(P, Q):
        ax.plot([p[0], q[0]], [p[1], q[1]], color="k", lw=0.5)
    ax.scatter([p[0] for p in P], [p[1] for p in P], marker="x", c="#cc3311", s=22,
               label="observed $p_t$ (from)", zorder=3)
    sc = ax.scatter([q[0] for q in Q], [q[1] for q in Q], c=[float(v) for v in y], cmap="viridis",
                    s=24, label="solution $q_t$ (to)", zorder=4)
    for t in sorted(moved, key=lambda t: -abs(out["theta"][t]))[:6]:
        ax.annotate(f"{years[t]}: {out['theta'][t]:+.3f}", (P[t][0], P[t][1]), fontsize=7,
                    xytext=(4, 4), textcoords="offset points")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set(xlabel="$p_K/p_{II}$", ylabel="$p_L/p_{II}$",
           title=f"one-sided profile: {len(moved)} of {T} years moved"
           + (f" (without {', '.join(map(str, drop))})" if drop else ""))
    ax.legend(loc="upper left", fontsize=7)
    fig.colorbar(sc, ax=ax, label="output $y_t$")
    suffix = "".join(f"_no{yr}" for yr in drop)
    fig.savefig(FIGURES / f"example_onesided{suffix}.png", dpi=150, bbox_inches="tight")


if __name__ == "__main__":
    main(tuple(int(a) for a in sys.argv[1:]))
