"""Shared helpers of the experiment scripts: output folder and the plotting functions
(hexagon and zonotope balls, weighted-solution panel).  matplotlib is imported lazily."""

import math
from pathlib import Path

RESULTS = Path(__file__).resolve().parent / "results"
RESULTS.mkdir(exist_ok=True)


def hexagon(p, rho):
    """Vertices (in the plane) of the hexagon {q : dhat(q, p) <= rho}, p = (p1, p2)."""
    l1, l2 = math.log(float(p[0])), math.log(float(p[1]))
    pts = [(rho, 0), (rho, rho), (0, rho), (-rho, 0), (-rho, -rho), (0, -rho)]
    return [(math.exp(l1 + a), math.exp(l2 + b)) for a, b in pts] + [
        (math.exp(l1 + pts[0][0]), math.exp(l2 + pts[0][1]))]


def zonotope(p, kappa_t, kappa0_t, rho):
    """Vertices (price space) of the ball {d_kappa <= rho} around p: log-box plus diagonal segment."""
    import numpy as np
    from scipy.spatial import ConvexHull

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
