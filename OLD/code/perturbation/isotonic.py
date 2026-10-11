"""The dominance relaxation as a disjunctive isotonic regression.

The dominance relaxation of the minimal perturbation problem is

    rho_dom = min pi(P, Q)  s.t.  for every pair y_t > y_s some i has q_t^i <= q_s^i,

a lower bound on rho (Lean: `le_of_dominates`, `isBlocked_singleton_iff`). For a fixed
choice sigma of the coordinate of every conflicting pair it splits into d independent
problems, one per coordinate i:

    min sum_t pi(p_t^i, q_t^i)  s.t.  q_t^i <= q_s^i  for the pairs with sigma = i,

an isotonic regression on a partial order with the loss pi(p, q) = max(q/p, p/q) - 1,
which is convex in ln q. So rho_dom = min over sigma of the sum of d isotonic
regressions. This module solves the isotonic regressions (a small convex program) and
the single-coordinate bound min_i IR_i(all conflicting pairs), which is feasible for
the relaxation, hence an upper bound on rho_dom.
"""

from __future__ import annotations

import heapq
import math
import time
from typing import TYPE_CHECKING

from pyscipopt import Model, quicksum

if TYPE_CHECKING:
    from .prep import Prepared

Pair = tuple[int, int]  # (t, s): q_t <= q_s is required


def isotonic(p: list[float], pairs: list[Pair], D: float = 1e3):
    """min sum_t pi(p_t, q_t) s.t. q_t <= q_s for (t, s) in pairs; (value, q)."""
    T = len(p)
    m = Model("isotonic")
    m.hideOutput()
    a = [m.addVar(f"a_{t}", lb=1 / (1 + D), ub=1 + D) for t in range(T)]
    g = [m.addVar(f"g_{t}", lb=0) for t in range(T)]
    for t in range(T):
        m.addCons(g[t] >= a[t] - 1)
        m.addCons(g[t] >= 1 / a[t] - 1)
    for t, s in pairs:
        m.addCons(p[t] * a[t] <= p[s] * a[s])
    m.setObjective(quicksum(g))
    m.setParam("numerics/feastol", 1e-9)
    m.setParam("limits/gap", 1e-9)
    m.optimize()
    return m.getObjVal(), [p[t] * m.getVal(a[t]) for t in range(T)]


def conflicts(prep: Prepared) -> list[Pair]:
    """Pairs (t, s) with y_t > y_s: q_t must not strictly dominate q_s."""
    y, T = prep.problem.y, prep.T
    return [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]


def fixed_assignment(prep: Prepared, sigma: dict[Pair, int]) -> float:
    """The relaxation with the coordinate of every conflicting pair fixed."""
    total = 0.0
    for i in range(prep.d):
        p = [row[i] for row in prep.P]
        total += isotonic(p, [pair for pair, j in sigma.items() if j == i])[0]
    return total


def dominance_bb(prep: Prepared, time_limit: float = 600.0, tol: float = 1e-9):
    """rho_dom by branch and bound over the choice sigma (Theorem split of the notes).

    A node fixes the coordinate of some conflicting pairs; its bound is the sum of the
    d isotonic regressions with those pairs only (a relaxation). If no conflicting pair
    is strictly dominated at the node solution, the node is feasible. Otherwise the
    most strictly dominated pair is branched on: d children, one per coordinate. A
    child changes one coordinate, so only that regression is recomputed.
    Returns (lower bound, best value, nodes, finished)."""
    d, P = prep.d, prep.P
    pairs = conflicts(prep)
    start = time.perf_counter()

    def solve(i: int, fixed: frozenset):
        return isotonic([row[i] for row in P], sorted(fixed))

    root = tuple(frozenset() for _ in range(d))
    sols = tuple(solve(i, root[i]) for i in range(d))
    heap = [(sum(v for v, _ in sols), 0, root, sols)]
    best, nodes, counter = math.inf, 0, 1
    while heap:
        if time.perf_counter() - start > time_limit:
            return heap[0][0], best, nodes, False
        bound, _, fixed, sols = heapq.heappop(heap)
        if bound >= best - tol:
            continue
        nodes += 1
        worst, pair = tol, None
        for t, s in pairs:
            gap = min(sols[i][1][t] - sols[i][1][s] for i in range(d))
            if gap > worst:
                worst, pair = gap, (t, s)
        if pair is None:
            best = bound
            continue
        for i in range(d):
            child = tuple(f | {pair} if j == i else f for j, f in enumerate(fixed))
            sol_i = solve(i, child[i])
            child_sols = tuple(sol_i if j == i else sols[j] for j in range(d))
            value = sum(v for v, _ in child_sols)
            if value < best - tol:
                heapq.heappush(heap, (value, counter, child, child_sols))
                counter += 1
    return best, best, nodes, True


def single_coordinate(prep: Prepared) -> tuple[float, int]:
    """min_i of the isotonic regression of coordinate i on all conflicting pairs, and
    the minimizing i: an upper bound on rho_dom."""
    pairs = conflicts(prep)
    values = [isotonic([row[i] for row in prep.P], pairs)[0] for i in range(prep.d)]
    i = min(range(prep.d), key=values.__getitem__)
    return values[i], i
