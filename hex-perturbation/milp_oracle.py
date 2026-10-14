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
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
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


# ---------------------------------------------------------------- column generation (PLACEHOLDER)


def price_milp(W, g, time_limit=None, max_retries=20):
    """Pricing: a weakly reachable S of W maximizing g(S) = sum_{r in S} g_r (one-set MILP, the
    same big-M witnesses as `oracle_milp`, each witness row divided by its M).  Returns (S, value),
    S checked exactly.  A set that fails the exact check (solver tolerance) is cut off by a no-good
    constraint and the MILP is solved again.

    NOTE (not for the paper): at d = 2 the failures seen before (10 of 63 BEA industries, T = 40)
    were caused by unscaled big-M rows; after dividing each witness row by its M, no set failed the
    exact check (0 cuts on all 63 industries).  At d = 7 (BEA, T = 40) sets DO fail the exact check
    again and 2 of 4 industries hit `max_retries`: the retry loop is not redundant there, but it is
    a workaround.  The proper fix is a pricing problem with exact geometry (lazy covering cuts
    x_t <= sum_{s in A} x_s, |A| <= d + 1), to be described in the paper instead of this loop."""
    n = len(W)
    d = len(W[0])
    Wf = np.array([[float(c) for c in w] for w in W])
    nv = n + n * d                             # x (n binaries), xi (n*d)

    def xi(t, i):
        return n + t * d + i

    rows, cols, vals, lb, ub = [], [], [], [], []
    row = 0
    for t in range(n):
        for i in range(d):
            rows.append(row); cols.append(xi(t, i)); vals.append(1.0)
        lb.append(1.0); ub.append(1.0); row += 1
        for s in range(n):
            if s == t:
                continue
            D = Wf[s] - Wf[t]
            M = float(np.max(np.abs(D)))
            if M == 0.0:
                continue
            for i in range(d):
                rows.append(row); cols.append(xi(t, i)); vals.append(float(D[i]) / M)
            rows += [row, row]; cols += [t, s]; vals += [-1.0, 1.0]
            lb.append(-1.0); ub.append(np.inf); row += 1
    c = np.zeros(nv)
    c[:n] = -np.asarray(g, dtype=float)
    integrality = np.zeros(nv)
    integrality[:n] = 1
    options = {} if time_limit is None else {"time_limit": time_limit}
    for _ in range(max_retries):
        A = coo_matrix((vals, (rows, cols)), shape=(row, nv)).tocsr()
        res = milp(c, constraints=LinearConstraint(A, lb, ub), integrality=integrality,
                   bounds=Bounds(np.zeros(nv), np.ones(nv)), options=options)
        if res.status != 0:
            raise RuntimeError(f"pricing MILP: {res.message}")
        S = frozenset(r for r in range(n) if res.x[r] > 0.5)
        if proj.is_weakly_reachable(W, S):
            return S, sum(float(g[r]) for r in S)
        price_milp.failures = getattr(price_milp, "failures", []) + [_interior_margin(Wf, S)]
        # no-good cut: sum_{r in S} (1 - x_r) + sum_{r not in S} x_r >= 1
        for r in range(n):
            rows.append(row); cols.append(r); vals.append(-1.0 if r in S else 1.0)
        lb.append(1.0 - len(S)); ub.append(np.inf); row += 1
        price_milp.cuts = getattr(price_milp, "cuts", 0) + 1
    raise RuntimeError("pricing MILP: too many sets failed the exact check")


def _interior_margin(Wf, S):
    """Diagnostics of a rejected set: max over t in S of the relative depth of W_t inside
    conv{W_s : s not in S} + R^d_+, i.e. max eps with sum lam_s W_s + eps W_t <= W_t (float LP)."""
    out = 0.0
    comp = [s for s in range(len(Wf)) if s not in S]
    for t in S:
        if not comp:
            break
        k = len(comp)
        A = np.hstack([Wf[comp].T, Wf[t][:, None]])          # sum lam W_s + eps W_t <= W_t
        res = linprog(np.r_[np.zeros(k), -1.0], A_ub=A, b_ub=Wf[t],
                      A_eq=np.r_[np.ones(k), 0.0][None, :], b_eq=[1.0],
                      bounds=[(0, None)] * k + [(None, 1.0)], method="highs")
        if res.status == 0:
            out = max(out, -res.fun)
    return out


def _master(columns, lo_rows, hi_rows, n):
    """Phase-1 LP: min sum of slacks s.t. sum_S m_S [r in S] + s_r >= lo_r, ... - s'_r <= hi_r.
    Returns (value, masses, y_lo, y_hi) with duals y >= 0 (scipy/HiGHS marginals)."""
    K = len(columns)
    nlo, nhi = len(lo_rows), len(hi_rows)
    A, b = [], []
    for j, (r, v) in enumerate(lo_rows):
        A.append([-float(r in S) for S in columns] + [-float(j == q) for q in range(nlo)] + [0.0] * nhi)
        b.append(-v)
    for j, (r, v) in enumerate(hi_rows):
        A.append([float(r in S) for S in columns] + [0.0] * nlo + [-float(j == q) for q in range(nhi)])
        b.append(v)
    c = [0.0] * K + [1.0] * (nlo + nhi)
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=(0, None), method="highs")
    if res.status != 0:
        raise RuntimeError(f"master LP: {res.message}")
    mu = -res.ineqlin.marginals               # >= 0
    y_lo = np.zeros(n)
    y_hi = np.zeros(n)
    for j, (r, _) in enumerate(lo_rows):
        y_lo[r] += mu[j]
    for j, (r, _) in enumerate(hi_rows):
        y_hi[r] += mu[nlo + j]
    return res.fun, res.x[:K], y_lo, y_hi


def oracle_cg(W, lo, hi, max_iter=1000, tol=1e-9, time_limit=None, columns=None):
    """PLACEHOLDER box oracle by column generation: LP master over weakly reachable sets found so
    far, pricing = `price_milp` with weights g = y_lo - y_hi.  Stops when no column has g(S) > tol:
    then the phase-1 value decides.  YES: exact masses on the support (`proj._cone_lp`).  NO: the
    Farkas vector lam = y_hi - y_lo (lam(S) >= -tol on all weakly reachable S up to the pricing
    MILP's optimality, float).  `columns`: optional warm-start sets (checked exactly)."""
    n = len(W)
    scale = max([1.0] + [abs(float(v)) for v in list(lo) + list(hi) if _finite(v)])
    lo_rows = [(r, float(v) / scale) for r, v in enumerate(lo) if _finite(v) and float(v) > 0]
    hi_rows = [(r, float(v) / scale) for r, v in enumerate(hi) if _finite(v)]
    if any(v < 0 for _, v in hi_rows):
        return proj.OracleAnswer(False)
    cols = [frozenset(range(n))]              # the full set is always weakly reachable
    for S in columns or []:
        if S not in cols and proj.is_weakly_reachable(W, S):
            cols.append(S)
    for it in range(max_iter):
        val, m, y_lo, y_hi = _master(cols, lo_rows, hi_rows, n)
        g = y_lo - y_hi
        S, gv = price_milp(W, g, time_limit)
        if gv <= tol or S in cols:
            break
        cols.append(S)
    else:
        raise RuntimeError("column generation: max_iter reached")
    oracle_cg.last_stats = {"iterations": it + 1, "columns": len(cols)}
    if val > 1e-7:
        lam = [F(float(a - b)).limit_denominator(10**9) for a, b in zip(y_hi, y_lo)]
        return proj.OracleAnswer(False, lam=lam)
    sets = [S for S, mm in zip(cols, m) if mm > tol]
    masses, _ = proj._cone_lp(sets, lo, hi)
    if masses is None:
        return proj.OracleAnswer(True)
    keep = [(S, mm) for S, mm in zip(sets, masses) if mm != 0]
    return proj.OracleAnswer(True, [S for S, _ in keep], [mm for _, mm in keep])
