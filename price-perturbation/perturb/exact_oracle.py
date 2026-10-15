"""Exact box oracle for any d >= 2: column generation with exact-geometry pricing.

    exists w in cone{1_S : S weakly reachable at the points W} with lo <= w <= hi    (proj.BoxOracle)

Why the placeholder `milp_oracle.oracle_cg` fails.  Its pricing MILP encodes the witnesses
<xi, W_s - W_t> >= 0 in floating point.  Near a breakpoint (and the lexicographic profile drives the
points exactly there: many points nearly share a coordinate) weak reachability is decided by exact
equalities, the solver accepts sets that are not weakly reachable, the exact check rejects them, and
the no-good loop does not end.

Exact geometry.  For S and t in S, t has no weak witness iff W_t in int K_S, K_S = conv{W_s : s not
in S} + R^d_+ (proj.is_weakly_reachable), i.e. iff some convex combination of points outside S is
strictly below W_t.  By Caratheodory it uses a set A of at most d + 1 points.  Such a pair (t, A)
gives the valid inequality ("cover cut")

    x_t <= sum_{s in A} x_s      (if t is in S, some point of A must be in S too),

and S is weakly reachable iff it satisfies all cover cuts.  The pricing MILP has binaries x_r and
cover cuts only: 0/1 coefficients, so its feasibility is not affected by solver tolerances.  Cuts are
generated lazily: a candidate S is checked exactly (rational LPs); for every t in int K_S a cut with
an exactly verified A is added.  The geometry is never decided in floating point.

Decision.  Column generation with a float LP master and this pricing until no column improves.  Then
an exact finish: the cone LP over the generated columns is solved in rationals (proj._cone_lp).
Feasible -> YES with exact masses.  Infeasible -> its exact Farkas vector lam; one more pricing with
the INTEGER weights -lam * lcm(denominators) looks for a weakly reachable S with lam(S) < 0.  Found ->
the column is added and the finish repeats.  Not found -> NO with lam.  With integer weights an
improving set has value >= 1, so the solver's objective tolerance cannot hide it (the weights are
kept below 2^50; otherwise the float weights are used and this is reported in `last_stats`).

Unsolvability measure.  The master value v = min over w in the cone of
sum_r (lo_r - w_r)^+ + (w_r - hi_r)^+ (scaled) is reported: every restricted master gives an upper
bound on v, and v = 0 iff the answer is YES.
"""

from __future__ import annotations

import math
from fractions import Fraction as F

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import coo_matrix

from . import proj
from .milp_oracle import _finite, _master

# ---------------------------------------------------------------- exact geometry


def _cover_value(W, t, A):
    """Exact max eps such that sum_{s in A} lam_s W_s + eps 1 <= W_t for some convex lam (None if no
    convex combination is <= W_t).  eps > 0 <=> conv(W_A) has a point strictly below W_t."""
    d = len(W[0])
    k = len(A)
    rows = []
    for i in range(d):          # sum lam W_s^i + sl_i + eps = W_t^i
        rows.append([F(W[s][i]) for s in A] + [F(int(i == j)) for j in range(d)] + [F(1)])
    rows.append([F(1)] * k + [F(0)] * (d + 1))
    b = [F(W[t][i]) for i in range(d)] + [F(1)]
    c = [F(0)] * (k + d) + [F(-1)]
    r = proj.simplex(rows, b, c)
    if r["status"] != "optimal":
        return None
    return -r["obj"]


def _exact_support(W, S, t):
    """Exact: if W_t in int K_S return a support A (|A| <= d + 1) of a convex combination strictly
    below W_t, else None.  Basic optimal solution of the LP of `_cover_value` over all s not in S."""
    d = len(W[0])
    rest = [s for s in range(len(W)) if s not in S]
    if not rest:
        return None
    rows = []
    for i in range(d):
        rows.append([F(W[s][i]) for s in rest] + [F(int(i == j)) for j in range(d)] + [F(1)])
    rows.append([F(1)] * len(rest) + [F(0)] * (d + 1))
    b = [F(W[t][i]) for i in range(d)] + [F(1)]
    c = [F(0)] * (len(rest) + d) + [F(-1)]
    r = proj.simplex(rows, b, c)
    if r["status"] != "optimal" or -r["obj"] <= 0:
        return None
    return [s for s, lam in zip(rest, r["x"][:len(rest)]) if lam != 0]


def _float_support(Wf, S, t):
    """Float LP: max eps with sum lam W_s + eps W_t <= W_t (relative), lam convex over s not in S.
    Returns (eps, support) or (None, None)."""
    rest = [s for s in range(len(Wf)) if s not in S]
    if not rest:
        return None, None
    k = len(rest)
    A = np.hstack([Wf[rest].T, Wf[t][:, None]])
    res = linprog(np.r_[np.zeros(k), -1.0], A_ub=A, b_ub=Wf[t], A_eq=np.r_[np.ones(k), 0.0][None, :],
                  b_eq=[1.0], bounds=[(0, None)] * k + [(None, 1.0)], method="highs-ds")
    if res.status != 0:
        return None, None
    return -res.fun, [s for s, lam in zip(rest, res.x[:k]) if lam > 1e-12]


def _float_witness(Wf, S, t):
    """Float LP: xi in the simplex maximising min_{s not in S} <xi, W_s - W_t> (rows scaled by their
    max norm).  Returns xi or None."""
    rest = [s for s in range(len(Wf)) if s not in S]
    if not rest:
        return np.ones(Wf.shape[1]) / Wf.shape[1]
    D = Wf[rest] - Wf[t]
    D = D / np.maximum(np.abs(D).max(axis=1, keepdims=True), 1e-300)
    d = Wf.shape[1]
    res = linprog(np.r_[np.zeros(d), -1.0], A_ub=np.hstack([-D, np.ones((len(rest), 1))]),
                  b_ub=np.zeros(len(rest)), A_eq=np.r_[np.ones(d), 0.0][None, :], b_eq=[1.0],
                  bounds=[(0, None)] * d + [(None, 1.0)], method="highs-ds")
    return res.x[:d] if res.status == 0 else None


def _exact_witness_ok(W, S, t, xi):
    """Exact check of a rounded witness: xi >= 0, xi != 0, <xi, W_s - W_t> >= 0 for all s not in S."""
    if xi is None:
        return False
    q = [F(float(v)).limit_denominator(10**6) if v > 1e-12 else F(0) for v in xi]
    if not any(q):
        return False
    Wt = W[t]
    for s in range(len(W)):
        if s not in S and sum(qi * (a - b) for qi, a, b in zip(q, W[s], Wt)) < 0:
            return False
    return True


class CoverCuts:
    """Cover cuts (t, A) for one point set W, exactly verified.  Starts with the pairwise cuts
    W_s < W_t (strictly, all coordinates) => x_t <= x_s, and with the `hints` (cuts found for other
    point sets) that are valid here (each re-verified exactly)."""

    def __init__(self, W, hints=()):
        self.W = [tuple(F(c) for c in w) for w in W]
        self.Wf = np.array([[float(c) for c in w] for w in W])
        self.cuts = set()
        n = len(W)
        for t in range(n):
            for s in range(n):
                if s != t and all(a < b for a, b in zip(self.W[s], self.W[t])):
                    self.cuts.add((t, (s,)))
        for t, A in hints:
            if (t, A) not in self.cuts and len(A) > 1:
                v = _cover_value(self.W, t, list(A))
                if v is not None and v > 0:
                    self.cuts.add((t, A))
        self.exact_checks = 0

    def separate(self, S):
        """Cuts violated by S (empty list <=> S weakly reachable, decided exactly)."""
        new = []
        for t in S:                                    # cheap: float support, exact verification
            eps, A = _float_support(self.Wf, S, t)
            if eps is not None and eps > 1e-9 and A and len(A) <= len(self.W[0]) + 1:
                v = _cover_value(self.W, t, A)
                if v is not None and v > 0:
                    new.append((t, tuple(sorted(A))))
        if not new:                                    # certify reachability exactly
            for t in S:
                if _exact_witness_ok(self.W, S, t, _float_witness(self.Wf, S, t)):
                    continue                           # exact witness found by rounding
                self.exact_checks += 1
                A = _exact_support(self.W, S, t)
                if A is not None:
                    new.append((t, tuple(sorted(A))))
        new = [c for c in new if c not in self.cuts]
        self.cuts.update(new)
        return new


# ---------------------------------------------------------------- pricing


def price_exact(cc, g, time_limit=None, max_rounds=10000):
    """max g(S) over weakly reachable S (exact feasibility).  g: floats or ints.  Returns (S, g(S)).
    The empty set (value 0) is allowed."""
    n = len(cc.W)
    c = -np.asarray(g, dtype=float)
    options = {"mip_rel_gap": 0.0}
    if time_limit is not None:
        options["time_limit"] = time_limit
    for _ in range(max_rounds):
        cuts = sorted(cc.cuts)
        if cuts:
            rows, cols, vals = [], [], []
            for k, (t, A) in enumerate(cuts):
                rows.append(k); cols.append(t); vals.append(1.0)
                for s in A:
                    rows.append(k); cols.append(s); vals.append(-1.0)
            M = coo_matrix((vals, (rows, cols)), shape=(len(cuts), n)).tocsr()
            cons = [LinearConstraint(M, -np.inf, 0.0)]
        else:
            cons = []
        res = milp(c, constraints=cons, integrality=np.ones(n), bounds=Bounds(np.zeros(n), np.ones(n)),
                   options=options)
        if res.status != 0:
            raise RuntimeError(f"exact pricing MILP: {res.message}")
        S = frozenset(r for r in range(n) if res.x[r] > 0.5)
        if not cc.separate(S):
            return S, float(sum(g[r] for r in S))
    raise RuntimeError("exact pricing: max_rounds reached")


# ---------------------------------------------------------------- oracle

_HINTS = {}      # (n, d) -> cover cuts of the last call; re-verified exactly before use


def oracle_exact(W, lo, hi, max_iter=10000, tol=1e-9, time_limit=None):
    """Exact box oracle (module docstring).  Returns proj.OracleAnswer with exact masses (YES) or
    an exact Farkas vector (NO).  oracle_exact.last_stats: iterations, columns, cuts, exact checks,
    finish rounds, master value (unsolvability measure, scaled), integer_weights flag."""
    n = len(W)
    cc = CoverCuts(W, _HINTS.get((n, len(W[0])), ()))
    scale = max([1.0] + [abs(float(v)) for v in list(lo) + list(hi) if _finite(v)])
    lo_rows = [(r, float(v) / scale) for r, v in enumerate(lo) if _finite(v) and float(v) > 0]
    hi_rows = [(r, float(v) / scale) for r, v in enumerate(hi) if _finite(v)]
    if any(float(v) < 0 for _, v in hi_rows):
        return proj.OracleAnswer(False)
    cols = [frozenset(range(n))]                      # the full set is always weakly reachable
    val = None
    it = 0
    for it in range(max_iter):
        val, m, y_lo, y_hi = _master(cols, lo_rows, hi_rows, n)
        if val <= tol:
            break
        S, gv = price_exact(cc, y_lo - y_hi, time_limit)
        if gv <= tol or S in cols:
            break
        cols.append(S)
    stats = {"iterations": it + 1, "master_value": float(val), "finish_rounds": 0,
             "integer_weights": True}
    while True:                                        # exact finish
        stats["finish_rounds"] += 1
        masses, lam = proj._cone_lp(cols, lo, hi)
        if masses is not None:
            keep = [(S, mm) for S, mm in zip(cols, masses) if mm != 0]
            ans = proj.OracleAnswer(True, [S for S, _ in keep], [mm for _, mm in keep])
            break
        den = 1
        for v in lam:
            den = den * F(v).denominator // math.gcd(den, F(v).denominator)
        w = [-(F(v) * den) for v in lam]               # integers; maximise -lam(S)
        if max(abs(x) for x in w) < 2**50:
            S, _ = price_exact(cc, [int(x) for x in w], time_limit)
        else:
            stats["integer_weights"] = False
            S, _ = price_exact(cc, [float(x) for x in w], time_limit)
        if sum(w[r] for r in S) > 0 and S not in cols:
            cols.append(S)
            continue
        ans = proj.OracleAnswer(False, lam=list(lam))
        break
    _HINTS[(n, len(W[0]))] = sorted(c for c in cc.cuts if len(c[1]) > 1)[:5000]
    stats.update({"columns": len(cols), "cuts": len(cc.cuts), "exact_checks": cc.exact_checks})
    oracle_exact.last_stats = stats
    return ans
