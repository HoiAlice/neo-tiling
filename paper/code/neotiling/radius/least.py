"""Least perturbation radius rho* for weak solvability (projective distance), with certificates.

`least_radius_exact`: exact rho* as 0.5 ln z*, z* a rational breakpoint (reach.breakpoints), by binary
search over the gaps between breakpoints; only boolean answers of the black-box oracle are used.
`least_radius_bisect`: float bisection.  `witness` / `refute`: exact YES / NO certificates.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction as F
from typing import Optional

from ..geometry.reach import (box_bounds, breakpoints, check_farkas, corners, gamma, gap_point, in_ball_exact,
                              is_weakly_reachable)
from ..oracle import OracleAnswer, as_answer


@dataclass
class Result:
    z_star: F                    # exact z* = e^{2 rho*} (1 if rho* = 0)
    rho: float                   # 0.5 ln z*
    gap: int                     # first feasible gap (-1: z = 1 itself feasible)
    k_below: F                   # rational k just below (k^2 in previous gap, or 1)
    k_above: F                   # rational k just above (k^2 in the first feasible gap)
    n_calls: int
    n_breakpoints: int
    roots: list = field(repr=False, default_factory=list)
    ans_below: Optional[OracleAnswer] = field(repr=False, default=None)
    ans_above: Optional[OracleAnswer] = field(repr=False, default=None)
    notes: list = field(default_factory=list)


def least_radius_exact(P, y, oracle, roots=None):
    """rho* = least rho with BOX(P e^{-rho}, P e^{rho}, y) feasible, exactly as 0.5 ln z*, z* a
    breakpoint (rational).  Uses only the boolean answers of the black-box `oracle(W, lo, hi)`:
    z = 1, then the last gap, then binary search over gaps (monotonicity).  O(log #breakpoints) calls."""
    P = [tuple(F(c) for c in p) for p in P]
    T = len(P)
    y = [F(v) for v in y]
    if roots is None:
        roots = breakpoints(P)
    m = len(roots)
    lo, hi = box_bounds(T, y)
    calls = [0]
    cache = {}
    notes = []

    def kk(i):
        return F(1) if i == -1 else gap_point(roots, i)

    def feasible(i):
        if i not in cache:
            calls[0] += 1
            cache[i] = as_answer(oracle(corners(P, kk(i)), lo, hi))
        return cache[i].feasible

    if feasible(-1):
        return Result(F(1), 0.0, -1, F(1), F(1), calls[0], m, roots, None, cache[-1], notes)
    if not feasible(m):
        raise RuntimeError("BOX infeasible even above the last breakpoint")
    lo_i, hi_i = -1, m
    while hi_i - lo_i > 1:
        mid = (lo_i + hi_i) // 2
        if feasible(mid):
            hi_i = mid
        else:
            lo_i = mid
    if hi_i == 0:
        notes.append("z=1 infeasible but gap 0 feasible (contradicts closedness)")
        z = F(1)
    else:
        z = roots[hi_i - 1]
    rho = 0.5 * (math.log(z.numerator) - math.log(z.denominator))
    return Result(z, rho, hi_i, kk(hi_i - 1), kk(hi_i), calls[0], m, roots,
                  cache.get(hi_i - 1) if hi_i - 1 >= -1 else None, cache[hi_i], notes)


def least_radius_bisect(P, y, oracle, tol=1e-6, rho_hi=1.0):
    """Bracket rho* to width `tol` by bisection in rho, without enumerating breakpoints (for large
    d, where there are C(2T+d, d+1) minors).  Rational query points k = e^{rho} (limit_denominator).
    Returns (rho_lo, rho_hi, calls): infeasible at rho_lo (or rho_lo = 0 feasible), feasible at rho_hi.
    Exactness would need bisection down to 1/H^2 (H = Hadamard bound of the minors) and a
    Stern-Brocot search for the unique breakpoint left; not implemented."""
    P = [tuple(F(c) for c in p) for p in P]
    T = len(P)
    lo, hi = box_bounds(T, [F(v) for v in y])
    calls = [0]

    def feasible(rho):
        calls[0] += 1
        k = F(math.exp(rho)).limit_denominator(10**9) if rho > 0 else F(1)
        return as_answer(oracle(corners(P, k), lo, hi)).feasible

    if feasible(0.0):
        return 0.0, 0.0, calls[0]
    a, b = 0.0, rho_hi
    while not feasible(b):
        a, b = b, 2 * b
    while b - a > tol:
        mid = (a + b) / 2
        if feasible(mid):
            b = mid
        else:
            a = mid
    return a, b, calls[0]


# ---------------------------------------------------------------- certificates


class CertificateError(Exception):
    pass


def witness(P, y, k, columns, masses):
    """YES certificate on the diagonal.  Input: exact columns (sets of corner indices, weakly reachable
    at W = (P/k, P k)) and exact masses with w(L_t) >= y_t >= w(U_t) (as supplied by the oracle).
    For every t: c*_t = max{c in [1/k, k] : sum_S m_S [c <= gamma(S, t)] >= y_t}, Q_t = c*_t p_t; the
    sets R_min,S = {t : c*_t < gamma(S,t)}, R_max,S = {t : c*_t <= gamma(S,t)} are split by the level
    sets of theta_t.  Everything is checked exactly.  Returns (Q, cert, checks) with cert a list of
    (S, m), S subsets of [T] weakly reachable at Q, sum m 1_S = y; raises CertificateError otherwise."""
    P = [tuple(F(c) for c in p) for p in P]
    y = [F(v) for v in y]
    k = F(k)
    T = len(P)
    W = corners(P, k)
    cols = [frozenset(S) for S in columns]
    masses = [F(m) for m in masses]
    if any(m < 0 for m in masses):
        raise CertificateError("negative mass")
    for t in range(T):
        if not (sum((m for S, m in zip(cols, masses) if t in S), F(0)) >= y[t]
                >= sum((m for S, m in zip(cols, masses) if T + t in S), F(0))):
            raise CertificateError("masses violate the corner inequalities")
    if not all(is_weakly_reachable(W, S) for S in cols):
        raise CertificateError("a column is not weakly reachable at the corners")
    gam = [[gamma(W, S, P[t]) for t in range(T)] for S in cols]

    def hi_fn(t, c):
        return sum((m for g, m in zip(gam, masses) if g[t] is None or c <= g[t]), F(0))

    cstar = []
    for t in range(T):
        cands = {k, 1 / k}
        for g in gam:
            if g[t] is not None and 1 / k <= g[t] <= k:
                cands.add(g[t])
        c = next((c for c in sorted(cands, reverse=True) if hi_fn(t, c) >= y[t]), None)
        if c is None:
            raise CertificateError("hi_t(1/k) < y_t")
        cstar.append(c)
    Q = [tuple(cstar[t] * x for x in P[t]) for t in range(T)]
    rmin = [frozenset(t for t in range(T) if g[t] is None or cstar[t] < g[t]) for g in gam]
    rmax = [frozenset(t for t in range(T) if g[t] is None or cstar[t] <= g[t]) for g in gam]
    theta = []
    for t in range(T):
        lo_t = sum((m for m, s in zip(masses, rmin) if t in s), F(0))
        hi_t = sum((m for m, s in zip(masses, rmax) if t in s), F(0))
        if not lo_t <= y[t] <= hi_t:
            raise CertificateError("y_t outside [lo, hi] at Q")
        theta.append((y[t] - lo_t) / (hi_t - lo_t) if hi_t > lo_t else F(0))
    cert = {}
    for m, lo_s, hi_s in zip(masses, rmin, rmax):
        levels = sorted({theta[t] for t in hi_s - lo_s if theta[t] > 0}, reverse=True)
        cs = levels + [F(0)]
        parts = [(lo_s, m * (1 - levels[0]))] if levels else [(lo_s, m)]
        for j, c in enumerate(levels):
            parts.append((lo_s | frozenset(t for t in hi_s - lo_s if theta[t] >= c), m * (c - cs[j + 1])))
        for S, mm in parts:
            if mm > 0:
                cert[S] = cert.get(S, F(0)) + mm
    cert = list(cert.items())
    checks = {
        "masses_sum_to_y": all(sum((m for S, m in cert if t in S), F(0)) == y[t] for t in range(T)),
        "sets_weakly_reachable_at_Q": all(is_weakly_reachable(Q, S) for S, _ in cert),
        "Q_in_ball": in_ball_exact(Q, P, k),
        "c_in_range": all(1 / k <= c <= k for c in cstar),
    }
    checks["ok"] = all(checks.values())
    return Q, cert, checks


def refute(P, y, k, lam, column_oracle=None, rationalize=True):
    """NO certificate at the corners W = (P/k, P k).  `lam` (floats or Fractions) is rationalised and
    checked: lam_{L_t} <= 0 <= lam_{U_t}, sum_t (lam_{L_t} + lam_{U_t}) y_t < 0 (exact), and
    lam(S) >= 0 for all weakly reachable S.  The last check cannot be done by this module for large
    instances: it is delegated to the optional `column_oracle(W, lam) -> min over weakly reachable S of
    lam(S)` (exact value expected; e.g. the user's MILP, or `column_oracle_brute`, or for d = 2
    `column_oracle_planar` which is exact).  Without a column oracle the entry `global_checked` is
    False and only the algebraic parts are verified.  Returns (lam_rational, checks)."""
    P = [tuple(F(c) for c in p) for p in P]
    T = len(P)
    y = [F(v) for v in y]
    W = corners(P, k)
    lo, hi = box_bounds(T, y)
    best = None
    for digits in (None, 4, 6, 8, 10, 12):
        if digits is None and not all(isinstance(v, F) for v in lam):
            continue
        lm = [F(v) if digits is None else F(v).limit_denominator(10 ** digits) for v in lam]
        lm = [min(F(0), v) if r < T else max(F(0), v) for r, v in enumerate(lm)]
        ok_alg = sum((lm[t] + lm[T + t]) * y[t] for t in range(T)) < 0 and check_farkas(None, lo, hi, lm)
        if not ok_alg:
            continue
        checks = {"signs": True, "objective_negative": True, "global_checked": False, "global_ok": None}
        if column_oracle is not None:
            mn = column_oracle(W, lm)
            checks["global_checked"] = True
            checks["global_ok"] = mn >= 0
            if checks["global_ok"]:
                return lm, checks
            best = (lm, checks)
            continue
        return lm, checks
    if best is not None:
        return best
    return None, {"signs": False, "objective_negative": False, "global_checked": False, "global_ok": None}
