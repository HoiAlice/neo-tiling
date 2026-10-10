"""Upper bounds: repair a point of the master to weakly solvable prices.

A master optimum Q* is cheap but, before the last iteration, not weakly solvable. The
repair keeps the decomposition of y over the spectra that are weakly reachable at Q*
(phase 1 of the column generation, which minimizes the residual mass) and adds the
singletons {t} for the residual, so y lies in the cone of the family F. With F and the
witnesses xi fixed, "every S in F is weakly reachable" is the set of linear constraints
<xi_{S,t}, q_s - q_t> >= 0, s not in S, and the cost is convex: a convex program, always
feasible (equal prices make every set weakly reachable). Alternating it with the choice
of the max-margin witnesses at the new prices never increases the cost.

The result is certified exactly by `cuts.certify_point`, so it is an upper bound on rho.
At the last iteration of the cut loop Q* itself is weakly solvable and the upper bound
meets the lower one.
"""

from __future__ import annotations

import math
from fractions import Fraction
from typing import TYPE_CHECKING

import numpy as np
from pyscipopt import Model, quicksum
from scipy.optimize import linprog

from .cuts import (
    MASS_EPS,
    ZERO,
    _float_witness,
    _Pricing,
    certify_point,
    covering,
)
from .verify import pert

if TYPE_CHECKING:
    from .prep import Prepared, Problem
    from .verify import Verification

REPAIR_D = 50.0  # box of the repair: a in [1/(1+D), 1+D]
FEASTOL = 1e-9
MAX_ROUNDS = 30


def residual_family(Q: list[list[float]], y: np.ndarray) -> list[frozenset[int]]:
    """Weakly reachable spectra at Q carrying as much of y as possible, plus the
    singletons of the residual: phase 1 of the column generation of `cuts.separate`."""
    T = len(Q)
    pricing = _Pricing(T)
    cols = [frozenset([t]) for t in range(T)]
    cols = [S for S in cols if all(covering(Q, S, t) is None for t in S)]
    while True:
        n = len(cols)
        A = np.array([[1.0 if t in S else 0.0 for S in cols] for t in range(T)])
        res = linprog(
            np.concatenate([np.zeros(n), np.ones(T)]),
            A_eq=np.hstack([A.reshape(T, n), np.eye(T)]),
            b_eq=y,
            bounds=[(0, None)] * (n + T),
            method="highs",
        )
        dual = np.array(res.eqlin.marginals)
        new = None
        while new is None:
            value, S = pricing.best(dual)
            if value <= ZERO:
                break
            bad = next(
                ((t, R) for t in S if (R := covering(Q, S, t)) is not None), None
            )
            if bad is None:
                new = S
            else:
                pricing.add(bad)
        if new is None:
            family = [S for S, v in zip(cols, res.x[:n]) if v > MASS_EPS]
            family += [
                frozenset([t])
                for t in range(T)
                if res.x[n + t] > MASS_EPS and frozenset([t]) not in family
            ]
            return family
        cols.append(new)


def _convex_step(P, family, witnesses):
    """min total perturbation s.t. <xi, q_s - q_t> >= 0 for the fixed witnesses."""
    T, d = len(P), len(P[0])
    m = Model("repair")
    m.hideOutput()
    a = {
        (t, i): m.addVar(f"a_{t}_{i}", lb=1 / (1 + REPAIR_D), ub=1 + REPAIR_D)
        for t in range(T)
        for i in range(d)
    }
    g = {k: m.addVar(f"g_{k[0]}_{k[1]}", lb=0) for k in a}
    for k, v in a.items():
        m.addCons(g[k] >= v - 1)
        m.addCons(g[k] >= 1 / v - 1)
    for k, S in enumerate(family):
        for t in S:
            xi = witnesses[k, t]
            for s in range(T):
                if s not in S:
                    m.addCons(
                        quicksum(
                            xi[i] * (P[s][i] * a[s, i] - P[t][i] * a[t, i])
                            for i in range(d)
                            if xi[i] > 0
                        )
                        >= 0
                    )
    m.setObjective(quicksum(g.values()))
    m.setParam("numerics/feastol", FEASTOL)
    m.optimize()
    if m.getStatus() != "optimal":
        return None, None
    A = [[m.getVal(a[t, i]) for i in range(d)] for t in range(T)]
    return A, m.getObjVal()


def repair(prep: Prepared, a) -> list[list[float]] | None:
    """Weakly solvable multipliers near the (not weakly solvable) multipliers a."""
    T, d, P = prep.T, prep.d, prep.P
    Q = [[P[t][i] * a[t][i] for i in range(d)] for t in range(T)]
    family = residual_family(Q, np.array(prep.y))
    best, value = None, None
    for _ in range(MAX_ROUNDS):
        witnesses = {}
        for k, S in enumerate(family):
            for t in S:
                xi = np.maximum(_float_witness(Q, S, t), 0)
                witnesses[k, t] = xi / xi.sum()
        A, v = _convex_step(P, family, witnesses)
        if A is None or (value is not None and v > value - ZERO):
            break  # no progress: keep the best point
        best, value = A, v
        Q = [[P[t][i] * A[t][i] for i in range(d)] for t in range(T)]
    return best


def strict_point(
    problem: Problem, check: Verification, deltas=(1e-9, 1e-8, 1e-7, 1e-6, 1e-5)
):
    """Strictly solvable prices near a certified weakly solvable answer (notes,
    lem:tilt): q_t - delta (sum_i ln q_t^i + delta y_t) e with the witnesses
    xi + delta / q_t, in coordinates scaled to max_t q_t^i = 1. Every witness margin
    is checked to be strictly positive in exact arithmetic, so y is solvable (not only
    weakly) at the returned prices. Returns (Q, pi(P, Q), delta) for the smallest delta
    that passes, or None."""
    T, d = problem.T, problem.d
    family = list(check.masses)
    scale = [max(check.Q[t][i] for t in range(T)) for i in range(d)]
    Qn = [[check.Q[t][i] / scale[i] for i in range(d)] for t in range(T)]
    Qf = [[float(c) for c in row] for row in Qn]
    ymax = max(problem.y) or Fraction(1)
    witnesses = {}
    for k, S in enumerate(family):
        for t in S:
            xi = np.maximum(_float_witness(Qf, S, t), 0)
            witnesses[k, t] = [Fraction(float(c)).limit_denominator(10**9) for c in xi]
    logs = [
        Fraction(sum(math.log(c) for c in row)).limit_denominator(10**12) for row in Qf
    ]
    for delta in map(Fraction, deltas):
        shift = [delta * (logs[t] + delta * problem.y[t] / ymax) for t in range(T)]
        Qd = [[Qn[t][i] - shift[t] for i in range(d)] for t in range(T)]
        if any(c <= 0 for row in Qd for c in row):
            continue
        strict = all(
            sum(
                (xi[i] + delta / Qn[t][i]) * (Qd[s][i] - Qd[t][i]) for i in range(d)
            )
            > 0
            for (k, t), xi in witnesses.items()
            for s in range(T)
            if s not in family[k]
        )
        if strict:
            Q = tuple(tuple(Qd[t][i] * scale[i] for i in range(d)) for t in range(T))
            total = sum(
                pert(problem.P[t][i], Q[t][i]) for t in range(T) for i in range(d)
            )
            return Q, total, delta
    return None


def upper_bound(problem: Problem, prep: Prepared, a) -> Verification | None:
    """An exactly certified weakly solvable answer near the multipliers a: a itself if
    it certifies, else its repair."""
    check = certify_point(problem, prep, a)
    if check is not None:
        return check
    A = repair(prep, a)
    return None if A is None else certify_point(problem, prep, A)
