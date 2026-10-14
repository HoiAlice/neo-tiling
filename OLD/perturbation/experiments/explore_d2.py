"""Exploration of rho(P, y) at d = 2 on small instances.

For small T we compute rho by enumerating candidate families F of weakly reachable
sets (|F| <= T, by Caratheodory). For each F:

1. Decide if y lies in cone{1_S : S in F} by an LP. Infeasible -> skip.
2. Minimize sum_{t,i} pi(P_{t,i}, Q_{t,i}) over positive Q and witnesses xi_{S,t}
   subject to <xi_{S,t}, q_s - q_t> >= 0 for every t in S, s not in S.

The inner problem is a convex perturbation cost with bilinear witness constraints
(SCIP solves it exactly up to its tolerances). The minimum over F is an upper bound
on rho; it equals rho once F spans the weakly reachable sets of some optimal Q.

For T = 3, 4, 5 this is tractable. The main purpose is to collect data and look for
patterns (dominance relaxation vs rho, structure of optimizers, hard instances).
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable

import numpy as np
from pyscipopt import Model, quicksum
from scipy.optimize import linprog

TOL = 1e-9
MASS_EPS = 1e-10


def pi(p: float, q: float) -> float:
    return max(q / p, p / q) - 1.0


def total_pi(P: np.ndarray, Q: np.ndarray) -> float:
    return float(sum(pi(P[t, i], Q[t, i]) for t in range(len(P)) for i in range(2)))


def y_in_cone(y: np.ndarray, family: list[frozenset[int]]) -> bool:
    """Is `y` in the cone spanned by indicators of sets in `family`?"""
    if not family:
        return all(abs(float(v)) < TOL for v in y)
    T = len(y)
    A = np.array([[1.0 if t in S else 0.0 for S in family] for t in range(T)])
    res = linprog(
        np.zeros(len(family)),
        A_eq=A,
        b_eq=np.asarray(y, dtype=float),
        bounds=[(0, None)] * len(family),
        method="highs",
    )
    return res.status == 0


def min_pi_fixed_family(
    P: np.ndarray, family: list[frozenset[int]], D: float = 50.0, time_limit: float = 60.0
) -> tuple[float, np.ndarray | None]:
    """min total_pi(P, Q) over positive Q such that every S in `family` is weakly
    reachable at Q (SCIP, exact up to its tolerances). D is a loose box bound."""
    T = len(P)
    m = Model("fixed_family")
    m.hideOutput()
    lo, hi = 1 / (1 + D), 1 + D
    a = {(t, i): m.addVar(f"a_{t}_{i}", lb=lo, ub=hi) for t in range(T) for i in range(2)}
    g = {(t, i): m.addVar(f"g_{t}_{i}", lb=0, ub=D) for t in range(T) for i in range(2)}
    for t in range(T):
        for i in range(2):
            m.addCons(g[t, i] >= a[t, i] - 1)
            m.addCons(g[t, i] >= 1 / a[t, i] - 1)  # convex on a > 0
    # Blocking by pairs: witnesses in the 2-simplex (one parameter xi in [0, 1]).
    # For singleton R = {s}: a disjunction q_t^0 <= q_s^0 OR q_t^1 <= q_s^1.
    for k, S in enumerate(family):
        others = [s for s in range(T) if s not in S]
        for t in S:
            # mixed witness xi = (lam, 1 - lam) in [0, 1]
            lam = m.addVar(f"lam_{k}_{t}", lb=0, ub=1)
            for s in others:
                diff0 = P[s, 0] * a[s, 0] - P[t, 0] * a[t, 0]
                diff1 = P[s, 1] * a[s, 1] - P[t, 1] * a[t, 1]
                # <xi, q_s - q_t> >= 0: lam * diff0 + (1 - lam) * diff1 >= 0.
                m.addCons(lam * diff0 + (1 - lam) * diff1 >= 0)
    m.setObjective(quicksum(g.values()))
    m.setParam("limits/time", time_limit)
    m.setParam("limits/gap", 1e-7)
    m.setParam("numerics/feastol", 1e-9)
    m.optimize()
    if m.getNSols() == 0:
        return math.inf, None
    A = np.array([[m.getVal(a[t, i]) for i in range(2)] for t in range(T)])
    Q = P * A
    return total_pi(P, Q), Q


def enumerate_small_families(T: int, max_size: int) -> Iterable[list[frozenset[int]]]:
    """All nonempty collections of nonempty, proper subsets of [T], up to size
    max_size. The universe and the empty set are trivial and never help."""
    subsets = [frozenset(S) for n in range(1, T) for S in itertools.combinations(range(T), n)]
    for k in range(1, max_size + 1):
        yield from itertools.combinations(subsets, k)


@dataclass
class Result:
    rho: float
    Q: np.ndarray | None
    family: list[frozenset[int]] | None
    checked: int


def rho_small(P: np.ndarray, y: np.ndarray, max_family_size: int = 4) -> Result:
    """Estimate rho by enumerating candidate families."""
    best_val, best_Q, best_F = math.inf, None, None
    checked = 0
    for F in enumerate_small_families(len(P), max_family_size):
        if not y_in_cone(y, list(F)):
            continue
        checked += 1
        value, Q = min_pi_fixed_family(P, list(F))
        if value < best_val - 1e-10:
            best_val, best_Q, best_F = value, Q, list(F)
    return Result(best_val, best_Q, best_F, checked)


def rho_dom(P: np.ndarray, y: np.ndarray) -> float:
    """Dominance relaxation: min total_pi(P, Q) s.t. for every (t, s) with y_t > y_s
    some coordinate i has q_t^i <= q_s^i. Enumerates sigma: conflict -> coord."""
    T = len(P)
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    best = math.inf
    for sigma in itertools.product((0, 1), repeat=len(conflicts)):
        D = 50.0
        m = Model("dom")
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
        m.setParam("numerics/feastol", 1e-9)
        m.setParam("limits/gap", 1e-7)
        m.optimize()
        if m.getStatus() == "optimal":
            best = min(best, m.getObjVal())
    return best


TRIANGLE_P = np.array([[4, 1], [3, 3], [1, 4]], dtype=float)
TRIANGLE_Y = np.array([1, 5, 3], dtype=float)


def check_triangle():
    """Known: rho = 2/5. Also known: rho_dom = 0 (no coordinate dominance)."""
    r = rho_small(TRIANGLE_P, TRIANGLE_Y, max_family_size=3)
    rd = rho_dom(TRIANGLE_P, TRIANGLE_Y)
    print(f"triangle: rho ~= {r.rho:.6f} (expected 0.4), rho_dom = {rd:.6f}")
    assert abs(r.rho - 0.4) < 1e-3, r
    assert abs(rd) < 1e-6, rd
    return r


if __name__ == "__main__":
    import sys
    if "--triangle" in sys.argv:
        check_triangle()
