"""Weighted perturbation with year-dependent penalty RATIOS (US data, d = 2): non-parallel steps.

The step of year t lies on the path theta -> p_t exp(theta v_t), v^i_t = 1/kappa^i_t + 1/kappa^0_t.
With penalties base_i * tau_t (us_weighted.py) all v_t are proportional and the steps are
parallel.  Here the capital penalty grows over time (its imputation improves), the others are
constant: kappa^K_t = 0.5 + 2.5 (t - t0)/(T - 1), kappa^L_t = kappa^II_t = 3.  Then v_t turns
from nearly horizontal (old years: capital moves) to the diagonal (2020: all prices equally).
Output: tex/figures/example_rot.png.  Run: ../.venv/bin/python experiments/us_rotating.py
"""

import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

from _common import FIGURES  # noqa: E402
from perturb import zono  # noqa: E402
from perturb.data import load_us_d2  # noqa: E402
from us_weighted import panel, solve  # noqa: E402


def rotating_weights(years):
    T = len(years)
    kappa = [[0.5 + 2.5 * t / (T - 1), 3.0] for t in range(T)]
    kappa0 = [3.0] * T
    return kappa, kappa0


def main():
    P, y, years = load_us_d2()
    P = [tuple(float(c) for c in p) for p in P]
    kap, k0 = rotating_weights(years)
    rho, w = solve(P, y, years, kap, k0)
    fig, ax = plt.subplots(figsize=(6.4, 5))
    sc = panel(ax, P, y, years, kap, k0, rho, w, f"capital penalty 0.5 → 3: $\\rho^*$ = {rho:.4f}")
    fig.colorbar(sc, ax=ax, label="output $y_t$")
    fig.savefig(FIGURES / "example_rot.png", dpi=150, bbox_inches="tight")
    print("year, slope of v_t (d ln(L/II) : d ln(K/II)), angle deg, step d ln(K/II), d ln(L/II)")
    for t, yr in enumerate(years):
        v = zono.path_vector(kap[t], k0[t])
        th = w["theta"][t]
        print(f"{yr} {v[1] / v[0]:.3f} {math.degrees(math.atan2(v[1], v[0])):5.1f} "
              f"{th * v[0]:+.4f} {th * v[1]:+.4f}")


if __name__ == "__main__":
    main()
