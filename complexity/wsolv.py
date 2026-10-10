"""Reference (brute-force) tools for weak solvability at fixed prices.

Notation follows latex/notes.tex, section "Weak solvability".  A set S of indices is weakly
reachable at prices P iff every t in S has a weak witness xi >= 0, xi != 0 with
<xi, p_s - p_t> >= 0 for all s outside S.  By the Ville/Gordan alternative this fails iff
p_t lies in conv{p_s : s notin S} + R^d_{++} ("t is strictly covered by the complement").
So S is weakly reachable iff its complement U is *closed*: no point outside U lies in
conv(p_U) + R^d_{++}.  The vector y is weakly solvable iff y lies in the cone spanned by the
indicators of weakly reachable sets.

Everything here is exponential in T and is used only as ground truth for small T.
"""

from __future__ import annotations

import itertools
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

Point = tuple  # tuple of ints / Fractions


# ---------------------------------------------------------------------------
# strict covering
# ---------------------------------------------------------------------------


def covered_lp(P: list[Point], t: int, R: list[int], tol: float = 1e-9) -> bool:
    """Is p_t in conv{p_r : r in R} + R^d_{++}?  (float LP, any d)."""
    if not R:
        return False
    d = len(P[t])
    # variables: w_r (r in R), s ; maximise s  s.t.  sum_r w_r p_r^i + s <= p_t^i
    n = len(R)
    c = np.zeros(n + 1)
    c[-1] = -1.0
    A = np.zeros((d, n + 1))
    b = np.zeros(d)
    for i in range(d):
        for k, r in enumerate(R):
            A[i, k] = float(P[r][i])
        A[i, -1] = 1.0
        b[i] = float(P[t][i])
    Aeq = np.zeros((1, n + 1))
    Aeq[0, :n] = 1.0
    bounds = [(0, None)] * n + [(None, 1e6)]
    res = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=[1.0], bounds=bounds, method="highs")
    assert res.status == 0, res.message
    return -res.fun > tol


def _pair_covers(p: Point, q: Point, target: Point, closed: bool = False) -> bool:
    """Exact: is there w in [0,1] with w p + (1-w) q < target (<= if closed) coordinatewise?"""
    lo, hi = Fraction(0), Fraction(1)
    lo_open = hi_open = False
    for a, b, c in zip(p, q, target):
        # w a + (1-w) b < c  <=>  w (a - b) < c - b
        a, b, c = Fraction(a), Fraction(b), Fraction(c)
        k, r = a - b, c - b
        if k == 0:
            if not (r >= 0 if closed else r > 0):
                return False
        elif k > 0:  # w < r/k
            v = r / k
            if v < hi or (v == hi and not hi_open):
                hi, hi_open = v, not closed
        else:  # w > r/k
            v = r / k
            if v > lo or (v == lo and not lo_open):
                lo, lo_open = v, not closed
    if lo < hi:
        return True
    return lo == hi and not lo_open and not hi_open


def covered_exact_2d(P: list[Point], t: int, R: list[int], closed: bool = False) -> bool:
    """Exact test for d = 2: covering by a set reduces to covering by a point or a pair.
    closed=False: p_t in conv + R^2_{++} (kills weak reachability);
    closed=True:  p_t in conv + R^2_+   (kills reachability)."""
    pt = P[t]
    for r in R:
        if all((Fraction(a) <= Fraction(b)) if closed else (Fraction(a) < Fraction(b))
               for a, b in zip(P[r], pt)):
            return True
    for r, s in itertools.combinations(R, 2):
        if _pair_covers(P[r], P[s], pt, closed):
            return True
    return False


def is_reachable(P: list[Point], S: frozenset[int], strict: bool = False) -> bool:
    """strict=False: weakly reachable (exact, d = 2 only); strict=True: reachable."""
    T = len(P)
    U = [s for s in range(T) if s not in S]
    return not any(covered_exact_2d(P, t, U, closed=strict) for t in S)


def family_2d(P: list[Point], strict: bool = False) -> list[frozenset[int]]:
    """All (weakly) reachable sets for d = 2, exact brute force over 2^T subsets."""
    T = len(P)
    return [S for mask in range(1 << T)
            if is_reachable(P, S := frozenset(i for i in range(T) if mask >> i & 1), strict)]


def is_weakly_reachable(P: list[Point], S: frozenset[int], exact2d: bool | None = None) -> bool:
    T = len(P)
    U = [s for s in range(T) if s not in S]
    if exact2d is None:
        exact2d = len(P[0]) == 2
    cov = covered_exact_2d if exact2d else covered_lp
    return not any(cov(P, t, U) for t in S)


def family(P: list[Point], exact2d: bool | None = None) -> list[frozenset[int]]:
    """All weakly reachable sets (brute force over 2^T subsets)."""
    T = len(P)
    out = []
    for mask in range(1 << T):
        S = frozenset(i for i in range(T) if mask >> i & 1)
        if is_weakly_reachable(P, S, exact2d):
            out.append(S)
    return out


# ---------------------------------------------------------------------------
# cone membership
# ---------------------------------------------------------------------------


def in_cone(sets: list[frozenset[int]], y, T: int, tol: float = 1e-9) -> bool:
    """Is y in cone{1_S : S in sets}?  Phase-one LP: min sum of residuals."""
    y = np.asarray([float(v) for v in y])
    sets = [S for S in sets if S]
    n = len(sets)
    if n == 0:
        return bool(np.all(np.abs(y) <= tol))
    A = np.zeros((T, n))
    for k, S in enumerate(sets):
        for t in S:
            A[t, k] = 1.0
    # A m + r+ - r- = y
    Aeq = np.hstack([A, np.eye(T), -np.eye(T)])
    c = np.concatenate([np.zeros(n), np.ones(2 * T)])
    res = linprog(c, A_eq=Aeq, b_eq=y, bounds=[(0, None)] * (n + 2 * T), method="highs")
    assert res.status == 0, res.message
    return res.fun <= tol * max(1.0, float(np.abs(y).sum()))


def max_weight(sets: list[frozenset[int]], w) -> Fraction:
    return max(sum((Fraction(w[t]) for t in S), Fraction(0)) for S in sets)
