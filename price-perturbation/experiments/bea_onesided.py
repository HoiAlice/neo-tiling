"""One-sided profile on BEA-BLS industries (d = 2, T = 40), weights zono.default_weights.

Question: does the profile collapse the solution onto a line p_i = const, as on the US data?
For each industry: rho*, stages, calls, sign pattern, and the spread (std over years) of
ln(p_K/p_II), ln(p_L/p_II) before and after.  Results are appended to
results/onesided_bea.jsonl (one line per industry); the figure tex/figures/example_onesided_bea.png
is drawn from all lines in that file.  Run (one industry at a time, long):
nice -n 19 ../.venv/bin/python experiments/bea_onesided.py [--exact] 15 24 6 63
nice -n 19 ../.venv/bin/python experiments/bea_onesided.py --plot
"""

import json
import sys
import time

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

from _common import FIGURES, RESULTS  # noqa: E402
from perturb import onesided, zono  # noqa: E402
from perturb.data import load_bea  # noqa: E402
from us_weighted import NAMES, flow  # noqa: E402

OUT = RESULTS / "onesided_bea.jsonl"


def spread(X, i):
    return float(np.std(np.log([x[i] for x in X])))


def run(ind, oracle=flow):
    P, y, years = load_bea(ind, d=2, T=40)
    P = [tuple(float(c) for c in p) for p in P]
    kap, k0 = zono.default_weights(years, 2, NAMES)
    t0 = time.time()
    out = onesided.profile(P, y, kap, k0, oracle, tol=1e-6,
                           log=lambda s: print(f"  [{time.time() - t0:.0f}s] {s}", flush=True))
    rec = {"ind": ind, "years": years, "P": P, "y": [float(v) for v in y], "Q": out["Q"],
           "theta": out["theta"], "rho": out["stages"][0]["lam"], "stages": len(out["stages"]),
           "calls": out["calls"], "time": round(time.time() - t0, 1), "ties": out["ties"],
           "verified": out["verified"], "tight": out["tight"], "both": out["both"],
           "spread_P": [spread(P, 0), spread(P, 1)], "spread_Q": [spread(out["Q"], 0), spread(out["Q"], 1)]}
    with open(OUT, "a") as f:
        f.write(json.dumps(rec) + "\n")
    signs = "".join("+" if th > 0 else "-" if th < 0 else "0" for th in out["theta"])
    print(f"BEA {ind}: rho* {rec['rho']:.5f}, {rec['stages']} stages, {rec['calls']} calls, {rec['time']}s, "
          f"ties {rec['ties']}, verified {rec['verified']}, tight {rec['tight']}, both {rec['both']}")
    print(f"  signs {years[0]}..{years[-1]}: {signs}")
    print(f"  std ln(K/II): {rec['spread_P'][0]:.4f} -> {rec['spread_Q'][0]:.4f}, "
          f"std ln(L/II): {rec['spread_P'][1]:.4f} -> {rec['spread_Q'][1]:.4f}", flush=True)


def plot():
    recs = [json.loads(line) for line in open(OUT)]
    n = len(recs)
    fig, axs = plt.subplots(1, n, figsize=(4.5 * n, 4.2), squeeze=False)
    for ax, r in zip(axs[0], recs):
        P, Q = r["P"], r["Q"]
        for p, q in zip(P, Q):
            ax.plot([p[0], q[0]], [p[1], q[1]], color="k", lw=0.4)
        ax.scatter([p[0] for p in P], [p[1] for p in P], marker="x", c="#cc3311", s=14, zorder=3)
        ax.scatter([q[0] for q in Q], [q[1] for q in Q], c=r["y"], cmap="viridis", s=16, zorder=4)
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.set(xlabel="$p_K/p_{II}$", title=f"BEA {r['ind']}: $\\rho^*$ = {r['rho']:.3f}")
    axs[0][0].set_ylabel("$p_L/p_{II}$")
    fig.savefig(FIGURES / "example_onesided_bea.png", dpi=150, bbox_inches="tight")


if __name__ == "__main__":
    if sys.argv[1:] == ["--plot"]:
        plot()
    else:
        args = sys.argv[1:]
        oracle = flow
        if args and args[0] == "--exact":              # exact_oracle.oracle_exact instead of the flow LP
            from perturb.exact_oracle import oracle_exact as oracle
            args = args[1:]
        for a in args:
            run(int(a), oracle)
