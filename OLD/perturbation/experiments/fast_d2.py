"""Fast rho and rho_dom computations for small d = 2 instances.

Design: avoid the exponential enumeration whenever possible.

* `rho_dom`: minimum of sum_{t, i} pi(p^i_t, q^i_t) subject to the dominance
  constraints "for every conflict (t, s) one coordinate has q^i_t <= q^i_s". We iterate
  over all `sigma: conflicts -> {0, 1}`, and for each sigma run a convex program
  with LINEAR order constraints (no bilinear terms). This is a convex sub-problem per
  sigma; solved by SciPy / CVXPY with a smooth log cost or by SCIP.

  Total conflicts c = |{(t, s) : y_t > y_s}|; enumeration 2^c. Tolerable up to c ~ 20.

* `rho_full`: enumerate candidate families F of weakly reachable sets, for each solve
  the convex-with-bilinear-witnesses sub-problem (SCIP). Scales to T <= 5-6.

Both routines return rational-ish approximations; good enough for exploration.
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass

import numpy as np
from pyscipopt import Model, quicksum
from scipy.optimize import linprog

TOL = 1e-9


def pi(p: float, q: float) -> float:
    return max(q / p, p / q) - 1.0


def total_pi(P: np.ndarray, Q: np.ndarray) -> float:
    T = len(P)
    return float(sum(pi(P[t, i], Q[t, i]) for t in range(T) for i in range(2)))


def _convex_isotonic(P: np.ndarray, sigma: list[int], conflicts: list[tuple[int, int]],
                     D: float = 100.0) -> tuple[float, np.ndarray | None]:
    """Minimise sum_{t,i} pi subject to the linear order constraints
    q^{sigma_k}_{t_k} <= q^{sigma_k}_{s_k} for every conflict k. Pure convex program."""
    T = len(P)
    m = Model("iso")
    m.hideOutput()
    lo, hi = 1 / (1 + D), 1 + D
    a = {(t, i): m.addVar(lb=lo, ub=hi) for t in range(T) for i in range(2)}
    g = {(t, i): m.addVar(lb=0, ub=D) for t in range(T) for i in range(2)}
    for t in range(T):
        for i in range(2):
            m.addCons(g[t, i] >= a[t, i] - 1)
            m.addCons(g[t, i] >= 1 / a[t, i] - 1)
    for (t, s), i in zip(conflicts, sigma):
        m.addCons(P[t, i] * a[t, i] <= P[s, i] * a[s, i])
    m.setObjective(quicksum(g.values()))
    m.setParam("limits/time", 20.0)
    m.setParam("limits/gap", 1e-8)
    m.setParam("numerics/feastol", 1e-9)
    m.optimize()
    if m.getStatus() != "optimal":
        return math.inf, None
    A = np.array([[m.getVal(a[t, i]) for i in range(2)] for t in range(T)])
    return total_pi(P, P * A), P * A


@dataclass
class DomResult:
    rho: float
    sigma: list[int] | None
    conflicts: list[tuple[int, int]]
    Q: np.ndarray | None


def rho_dom_exact(P: np.ndarray, y: np.ndarray) -> DomResult:
    """Exact rho_dom by enumerating sigma."""
    T = len(P)
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    if not conflicts:
        return DomResult(0.0, [], [], P.copy())
    best_val, best_sigma, best_Q = math.inf, None, None
    for sigma in itertools.product((0, 1), repeat=len(conflicts)):
        v, Q = _convex_isotonic(P, list(sigma), conflicts)
        if v < best_val - 1e-10:
            best_val, best_sigma, best_Q = v, list(sigma), Q
    return DomResult(best_val, best_sigma, conflicts, best_Q)


def _y_in_cone(y: np.ndarray, family: list[frozenset[int]]) -> bool:
    T = len(y)
    if not family:
        return all(abs(float(v)) < TOL for v in y)
    A = np.array([[1.0 if t in S else 0.0 for S in family] for t in range(T)])
    res = linprog(
        np.zeros(len(family)), A_eq=A, b_eq=np.asarray(y, dtype=float),
        bounds=[(0, None)] * len(family), method="highs",
    )
    return res.status == 0


def _min_pi_mixed(P: np.ndarray, family: list[frozenset[int]],
                  D: float = 50.0) -> float:
    """Min pi over positive Q with xi_{S,t} in the 2-simplex making every S weakly
    reachable. One continuous lam in [0, 1] per (S, t) (bilinear). SCIP."""
    T = len(P)
    m = Model("mixed")
    m.hideOutput()
    lo, hi = 1 / (1 + D), 1 + D
    a = {(t, i): m.addVar(lb=lo, ub=hi) for t in range(T) for i in range(2)}
    g = {(t, i): m.addVar(lb=0, ub=D) for t in range(T) for i in range(2)}
    for t in range(T):
        for i in range(2):
            m.addCons(g[t, i] >= a[t, i] - 1)
            m.addCons(g[t, i] >= 1 / a[t, i] - 1)
    for k, S in enumerate(family):
        others = [s for s in range(T) if s not in S]
        for t in S:
            lam = m.addVar(f"lam_{k}_{t}", lb=0, ub=1)
            for s in others:
                d0 = P[s, 0] * a[s, 0] - P[t, 0] * a[t, 0]
                d1 = P[s, 1] * a[s, 1] - P[t, 1] * a[t, 1]
                m.addCons(lam * d0 + (1 - lam) * d1 >= 0)
    m.setObjective(quicksum(g.values()))
    m.setParam("limits/time", 30.0)
    m.setParam("limits/gap", 1e-7)
    m.setParam("numerics/feastol", 1e-9)
    m.optimize()
    if m.getNSols() == 0:
        return math.inf
    A = np.array([[m.getVal(a[t, i]) for i in range(2)] for t in range(T)])
    return total_pi(P, P * A)


@dataclass
class FullResult:
    rho: float
    family: list[frozenset[int]] | None


def rho_full_small(P: np.ndarray, y: np.ndarray, max_family_size: int = 4) -> FullResult:
    """Enumerate families of nonempty proper subsets, |F| <= max_family_size."""
    T = len(P)
    subsets = [frozenset(S) for n in range(1, T) for S in itertools.combinations(range(T), n)]
    best_val, best_F = math.inf, None
    for k in range(1, max_family_size + 1):
        for F in itertools.combinations(subsets, k):
            if not _y_in_cone(y, list(F)):
                continue
            value = _min_pi_mixed(P, list(F))
            if value < best_val - 1e-10:
                best_val, best_F = value, list(F)
    return FullResult(best_val, best_F)


if __name__ == "__main__":
    import sys
    P = np.array([[4, 1], [3, 3], [1, 4]], float)
    y = np.array([1, 5, 3], float)
    r = rho_dom_exact(P, y)
    print(f"triangle rho_dom = {r.rho:.6f} sigma = {r.sigma} (expected 0)")
    f = rho_full_small(P, y, max_family_size=3)
    print(f"triangle rho_full = {f.rho:.6f} (expected 0.4) family = {[sorted(S) for S in f.family or []]}")
