"""PLACEHOLDER weak-solvability oracle for any d >= 2: one MILP (HiGHS via scipy.optimize.milp).

This is a temporary stand-in for the user's MILP oracle, to be replaced.  It follows the
formulation of OLD/code/perturbation/model.py at FIXED prices, with the equality sum_k w = y
replaced by the bounds lo <= w <= hi of the `proj.BoxOracle` interface:

    exists w in cone{1_S : S weakly reachable at the points W} with lo <= w <= hi.

Variables, for sets k in [K] and points r, t in [n] (n = |W|):
  z[k,r] binary          S_k = {r | z[k,r] = 1}
  m[k] in [0, Y]         mass of S_k
  v[k,r] in [0, Y]       v = m z (McCormick, exact for binary z)
  xi[k,t,:] in simplex   weak witness of t in S_k
Constraints:
  sum_i xi[k,t,i] (W_s^i - W_t^i) >= -M_st (1 - z[k,t] + z[k,s])   for s != t,
  M_st = max_i |W_s^i - W_t^i|  (enough, since xi lies in the simplex),
  lo_r <= sum_k v[k,r] <= hi_r.
K = n sets suffice (Caratheodory in R^n).  Mass bound Y = max of the finite entries of lo and hi:
a set with mass > Y can only contain indices with hi = inf, and lowering its mass to Y keeps
w_r >= Y >= lo_r there, so the bound loses no solutions.

The decision is a FLOAT decision of the MILP solver.  A YES answer is turned into an exact
certificate when possible: the support sets are checked exactly (`proj.is_weakly_reachable`) and
the masses recomputed exactly (`proj._cone_lp`).  A NO answer carries no Farkas vector.
"""

from __future__ import annotations

import math
from fractions import Fraction as F

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

import proj


def _finite(v):
    return not math.isinf(float(v))


def oracle_milp(W, lo, hi, K=None, time_limit=None, tol=1e-6):
    """PLACEHOLDER box oracle (see module docstring).  Returns a `proj.OracleAnswer`."""
    n = len(W)
    d = len(W[0])
    K = n if K is None else K
    Wf = np.array([[float(c) for c in w] for w in W])
    lo_f = np.array([float(v) for v in lo])
    hi_f = np.array([float(v) for v in hi])
    if np.any(lo_f > hi_f):
        return proj.OracleAnswer(False)
    Y = max([0.0] + [abs(float(v)) for v in list(lo) + list(hi) if _finite(v)])
    if Y == 0.0:
        return proj.OracleAnswer(True, [], [])

    # variable layout, per set k: z (n), m (1), v (n), xi (n*d)
    blk = 2 * n + 1 + n * d
    nv = K * blk

    def z(k, r):
        return k * blk + r

    def m(k):
        return k * blk + n

    def v(k, r):
        return k * blk + n + 1 + r

    def xi(k, t, i):
        return k * blk + 2 * n + 1 + t * d + i

    rows, cols, vals, lb, ub = [], [], [], [], []
    row = 0

    def add(entries, l, u):
        nonlocal row
        for c, a in entries:
            rows.append(row)
            cols.append(c)
            vals.append(a)
        lb.append(l)
        ub.append(u)
        row += 1

    for k in range(K):
        for r in range(n):
            add([(v(k, r), 1.0), (z(k, r), -Y)], -np.inf, 0.0)               # v <= Y z
            add([(v(k, r), 1.0), (m(k), -1.0)], -np.inf, 0.0)                # v <= m
            add([(m(k), 1.0), (v(k, r), -1.0), (z(k, r), Y)], -np.inf, Y)    # v >= m - Y (1 - z)
        for t in range(n):
            add([(xi(k, t, i), 1.0) for i in range(d)], 1.0, 1.0)            # xi in the simplex
            for s in range(n):
                if s == t:
                    continue
                D = Wf[s] - Wf[t]
                M = float(np.max(np.abs(D)))
                if M == 0.0:
                    continue
                add([(xi(k, t, i), float(D[i])) for i in range(d)] + [(z(k, t), -M), (z(k, s), M)],
                    -M, np.inf)
        if k + 1 < K:
            add([(m(k), 1.0), (m(k + 1), -1.0)], 0.0, np.inf)                # symmetry: m decreasing
    for r in range(n):
        add([(v(k, r), 1.0) for k in range(K)], lo_f[r], hi_f[r])           # lo <= w <= hi

    A = coo_matrix((vals, (rows, cols)), shape=(row, nv)).tocsr()
    integrality = np.zeros(nv)
    lower, upper = np.zeros(nv), np.full(nv, Y)
    for k in range(K):
        for r in range(n):
            integrality[z(k, r)] = 1
            upper[z(k, r)] = 1.0
        for t in range(n):
            for i in range(d):
                upper[xi(k, t, i)] = 1.0
    options = {} if time_limit is None else {"time_limit": time_limit}
    res = milp(np.zeros(nv), constraints=LinearConstraint(A, lb, ub), integrality=integrality,
               bounds=Bounds(lower, upper), options=options)
    if res.status == 2:                       # infeasible
        return proj.OracleAnswer(False)
    if res.x is None:
        raise RuntimeError(f"MILP oracle: no decision ({res.message})")

    # exact certificate from the support
    x = res.x
    sets = []
    for k in range(K):
        if x[m(k)] > tol:
            S = frozenset(r for r in range(n) if x[z(k, r)] > 0.5)
            if S and S not in sets and proj.is_weakly_reachable(W, S):
                sets.append(S)
    masses, _ = proj._cone_lp(sets, lo, hi)
    if masses is None:
        return proj.OracleAnswer(True)        # float YES without an exact certificate
    keep = [(S, mm) for S, mm in zip(sets, masses) if mm != 0]
    return proj.OracleAnswer(True, [S for S, _ in keep], [mm for _, mm in keep])
