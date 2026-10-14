"""Least perturbation radius for weak solvability at arbitrary fixed d >= 2 (projective distance).

Prices are (d+1)-dimensional, normalised by the last coordinate to p_t in R^d_{++}.  The distance of
normalised points is dist(a, b) = min_t sum_{i<d} |u_i + t| + |t|, u_i = ln a_i - ln b_i, i.e. the sum
of absolute deviations of the d+1 numbers (u_1, .., u_d, 0) from their median.

Facts used (README.md, section "General d"):
  1. {dist <= rho} lies in the cube |u_i| <= rho and contains the diagonal u = (s, .., s), |s| <= rho.
     By the box theorem, feasibility with dist-balls of radius rho <=> BOX(p e^{-rho}, p e^{rho}, y).
  2. Corners (P/k, P k), z = k^2 = e^{2 rho}.
  3. Weak reachability of S at W depends only on the oriented matroid of the vectors (W_r, 1) and
     (e_i, 0).  Every (d+1)x(d+1) determinant of such vectors is a polynomial in z.  FINDING (differs
     from the brief): it is always z^{b-1} (D0 z + D1), because the rows (z x, 1) = (z x, 0) + (0, 1)
     differ from the rows (x, 1) by a rank-one term in the last coordinate.  So every breakpoint is
     RATIONAL, no algebraic numbers, no factorisation are needed.
  4. Entry scale gamma(S, t) = min{c >= 0 : c p_t in conv{W_r : r not in S} + R^d_+} (exact LP).

The weak-solvability oracle is a BLACK BOX:  BoxOracle = Callable[[W, lo, hi], bool | OracleAnswer]
"exists w in cone{1_S : S weakly reachable at the points W} with lo <= w <= hi componentwise"
(lo/hi over the 2T corner indices, entries may be -inf/+inf).  Plain weak solvability: lo = hi = y.
The BOX form: lo = (y, 0), hi = (inf, y) over (L_1..L_T, U_1..U_T), see `box_bounds`.  An oracle may
return an `OracleAnswer` with a certificate (columns + masses for YES, lam for NO); certificates are
used only if supplied.  Reference oracles for testing: `oracle_brute` (any d, exact, 2^|W| sets) and
`oracle_flow` (d = 2, box form only, via box.py).
"""

from __future__ import annotations

import itertools
import math
import sys
import time
from dataclasses import dataclass, field
from fractions import Fraction as F
from pathlib import Path
from typing import Callable, Optional

INF = float("inf")

# ---------------------------------------------------------------- distance


def dist(a, b):
    """dist(a, b): sum of |v - median| over v in (ln a_1 - ln b_1, .., ln a_d - ln b_d, 0) (float)."""
    v = [math.log(float(x)) - math.log(float(y)) for x, y in zip(a, b)] + [0.0]
    med = sorted(v)[len(v) // 2]
    return sum(abs(x - med) for x in v)


def in_ball(Q, P, rho, tol=1e-12):
    """max_t dist(q_t, p_t) <= rho (float, tiny tolerance)."""
    return all(dist(q, p) <= rho + tol for q, p in zip(Q, P))


def in_ball_exact(Q, P, k):
    """Exact test for rational k = e^rho: with r_i = q_i / p_i and m the median of (r_1..r_d, 1),
    dist <= ln k  <=>  prod_j max(r_j / m, m / r_j) <= k, over all t."""
    k = F(k)
    for q, p in zip(Q, P):
        r = [F(a) / F(b) for a, b in zip(q, p)] + [F(1)]
        m = sorted(r)[len(r) // 2]
        prod = F(1)
        for x in r:
            prod *= max(x / m, m / x)
        if prod > k:
            return False
    return True


# ---------------------------------------------------------------- exact rational simplex


def simplex(A, b, c=None):
    """Exact two-phase simplex (Fractions, Bland's rule) for: min c.x s.t. A x = b, x >= 0.
    Intended for tiny certification LPs.  Returns a dict with
      status: 'optimal' | 'infeasible' | 'unbounded',
      x, obj (optimal), and for 'infeasible' a Farkas vector `pi` (original row signs) with
      pi^T A_j <= 0 for all columns j and pi . b > 0."""
    m = len(A)
    n = len(A[0]) if m else (len(c) if c else 0)
    if m == 0:
        if c and any(ci < 0 for ci in c):
            return {"status": "unbounded"}
        return {"status": "optimal", "x": [F(0)] * n, "obj": F(0)}
    sgn = [1 if F(bi) >= 0 else -1 for bi in b]
    tab = [[F(sgn[i]) * F(a) for a in A[i]] + [F(int(i == j)) for j in range(m)] + [F(sgn[i]) * F(b[i])]
           for i in range(m)]
    basis = [n + i for i in range(m)]
    ncol = n + m

    def pivot(r, j):
        pr = tab[r]
        pv = pr[j]
        if pv != 1:
            pr[:] = [x / pv for x in pr]
        for i in range(len(tab)):
            if i != r and tab[i][j] != 0:
                f = tab[i][j]
                ti = tab[i]
                tab[i] = [x - f * y for x, y in zip(ti, pr)]
        basis[r] = j

    def run(cost, allowed):
        while True:
            cb = [cost[bj] for bj in basis]
            enter = None
            for j in allowed:
                if j in bset():
                    continue
                red = cost[j] - sum((cb[i] * tab[i][j] for i in range(len(tab)) if cb[i] != 0 and tab[i][j] != 0),
                                    F(0))
                if red < 0:
                    enter = j
                    break
            if enter is None:
                return "optimal"
            best = None
            for i in range(len(tab)):
                a = tab[i][enter]
                if a > 0:
                    ratio = tab[i][-1] / a
                    if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]):
                        best = (ratio, i)
            if best is None:
                return "unbounded"
            pivot(best[1], enter)

    def bset():
        return set(basis)

    cost1 = [F(0)] * n + [F(1)] * m
    run(cost1, range(n))
    obj1 = sum((cost1[basis[i]] * tab[i][-1] for i in range(len(tab))), F(0))
    if obj1 > 0:
        pi = [sum((cost1[basis[k]] * tab[k][n + i] for k in range(len(tab))), F(0)) * sgn[i] for i in range(m)]
        return {"status": "infeasible", "pi": pi}
    # drive artificial variables out of the basis
    i = 0
    while i < len(tab):
        if basis[i] >= n:
            j = next((j for j in range(n) if tab[i][j] != 0), None)
            if j is None:
                del tab[i]
                del basis[i]
                continue
            pivot(i, j)
        i += 1
    if c is None:
        c = [F(0)] * n
    cost2 = [F(v) for v in c] + [F(0)] * m
    st = run(cost2, range(n))
    if st == "unbounded":
        return {"status": "unbounded"}
    x = [F(0)] * n
    for i, bj in enumerate(basis):
        if bj < n:
            x[bj] = tab[i][-1]
    return {"status": "optimal", "x": x, "obj": sum((F(ci) * xi for ci, xi in zip(c, x)), F(0))}


def _vec(x):
    return tuple(F(v) for v in x)


def _in_interior(W, S, t):
    """Is W_t in int K_S, K_S = conv{W_r : r not in S} + R^d_+ ?  (K_S empty: no.)
    LP: min tau' s.t. sum_s w_s W_s + sl - tau' 1 = W_t - B 1, sum w = 1, w >= 0 (tau = tau' - B);
    W_t is interior iff the optimum tau < 0."""
    d = len(W[0])
    rest = [s for s in range(len(W)) if s not in S]
    if not rest:
        return False
    Wt = W[t]
    B = max(Wt)
    nr = len(rest)
    A = []
    for i in range(d):
        A.append([F(W[s][i]) for s in rest] + [F(int(i == j)) for j in range(d)] + [F(-1)])
    A.append([F(1)] * nr + [F(0)] * (d + 1))
    bvec = [F(Wt[i]) - B for i in range(d)] + [F(1)]
    cost = [F(0)] * (nr + d) + [F(1)]
    r = simplex(A, bvec, cost)
    return r["status"] == "optimal" and r["obj"] < B


def is_weakly_reachable(W, S):
    """Exact: S (set of indices) is weakly reachable at the points W (tuples of Fractions): for every
    t in S there is xi >= 0, xi != 0 with <xi, W_s - W_t> >= 0 for all s not in S.  By Ville's theorem
    this is equivalent to W_t not in int(conv{W_s : s not in S} + R^d_+) (one tiny LP per t)."""
    S = set(S)
    return all(not _in_interior(W, S, t) for t in S)


def is_weakly_reachable_direct(W, S):
    """Same by the definition (direct LP for xi); used to cross-check `is_weakly_reachable`."""
    S = set(S)
    d = len(W[0])
    rest = [s for s in range(len(W)) if s not in S]
    for t in S:
        A = [[F(1)] * d + [F(0)] * len(rest)]
        for j, s in enumerate(rest):
            A.append([F(W[s][i]) - F(W[t][i]) for i in range(d)] + [F(-int(j == jj)) for jj in range(len(rest))])
        r = simplex(A, [F(1)] + [F(0)] * len(rest))
        if r["status"] != "optimal":
            return False
    return True


def gamma(W, S, p):
    """Exact gamma(S, p) = min{c >= 0 : c p in conv{W_r : r not in S} + R^d_+}; None = +infinity
    (K_S empty)."""
    d = len(W[0])
    rest = [s for s in range(len(W)) if s not in set(S)]
    if not rest:
        return None
    nr = len(rest)
    A = []
    for i in range(d):
        A.append([F(W[s][i]) for s in rest] + [F(int(i == j)) for j in range(d)] + [-F(p[i])])
    A.append([F(1)] * nr + [F(0)] * (d + 1))
    r = simplex(A, [F(0)] * d + [F(1)], [F(0)] * (nr + d) + [F(1)])
    assert r["status"] == "optimal"
    return r["obj"]


# ---------------------------------------------------------------- breakpoints


def _det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    if n == 3:
        a, b, c = M[0]
        d, e, f = M[1]
        g, h, i = M[2]
        return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)
    if n == 4:
        tot = 0
        r0 = M[0]
        for j in range(4):
            if r0[j] == 0:
                continue
            m3 = [[row[k] for k in range(4) if k != j] for row in M[1:]]
            tot += (-1) ** j * r0[j] * _det(m3)
        return tot
    # Bareiss
    M = [list(r) for r in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if M[i][k] != 0), None)
            if sw is None:
                return 0
            M[k], M[sw] = M[sw], M[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


def det_poly(P, idx, upper, J):
    """Exact determinant of the vectors (z^{u_r} p_{t_r}[J], 1) as a polynomial in z, by
    interpolation at z = 0..len(idx) (reference implementation for tests).  idx: point indices,
    upper: 0/1 flags.  P Fractions.  Returns coefficient list (Fractions), degree <= len(idx)."""
    k = len(idx)
    pts = list(range(k + 1))
    vals = []
    for zv in pts:
        M = [[F(P[t][i]) * (zv if u else 1) for i in J] + [F(1)] for t, u in zip(idx, upper)]
        vals.append(_det_frac(M))
    # Newton -> monomial coefficients
    n = len(pts)
    coef = [F(0)] * n
    basis = [F(1)]
    # Lagrange by solving Vandermonde with Fractions
    A = [[F(zv) ** j for j in range(n)] + [vals[i]] for i, zv in enumerate(pts)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        A[c] = [x / A[c][c] for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [A[i][-1] for i in range(n)]


def _det_frac(M):
    n = len(M)
    M = [list(r) for r in M]
    det = F(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            det = -det
        det *= M[c][c]
        for r in range(c + 1, n):
            if M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return det


def breakpoints(P, return_stats=False):
    """All breakpoints z > 1, as a strictly increasing list of Fractions.  Enumerates the
    (d+1)-subsets of the 2T + d homogenised vectors (p_t, 1), (z p_t, 1), (e_i, 0) grouped by the set J
    of coordinates not removed by e_i (a subset of m+1 corners and a coordinate set J, |J| = m, gives
    the minor on (x_J, 1)).  Subsets with a lower and b upper corners give z^{b-1}(D0 z + D1) with
    D0 + D1 = det at z = 1 and 2^{b-1}(2 D0 + D1) = det at z = 2; root z = -D1 / D0.
    Constant polynomials (b = 0, or all rows upper) have no root > 1."""
    t0 = time.time()
    P = [tuple(F(c) for c in p) for p in P]
    T, d = len(P), len(P[0])
    X = []
    scale = []
    for i in range(d):
        den = 1
        for p in P:
            den = den * p[i].denominator // math.gcd(den, p[i].denominator)
        scale.append(den)
    X = [[int(p[i] * scale[i]) for i in range(d)] for p in P]
    n_total = math.comb(2 * T + d, d + 1)
    polys, roots = set(), set()
    n_eval = 0
    for m in range(1, d + 1):
        for J in itertools.combinations(range(d), m):
            r1 = [[X[t][i] for i in J] + [1] for t in range(T)]
            r2 = [[2 * X[t][i] for i in J] + [1] for t in range(T)]
            for b in range(1, m + 1):
                a = m + 1 - b
                for A_ in itertools.combinations(range(T), a):
                    for B_ in itertools.combinations(range(T), b):
                        M1 = [r1[t] for t in A_] + [r1[t] for t in B_]
                        M2 = [r1[t] for t in A_] + [r2[t] for t in B_]
                        d1 = _det(M1)
                        d2 = _det(M2)
                        n_eval += 1
                        # det(1) = D0 + D1, det(2) = 2^{b-1}(2 D0 + D1)
                        e2 = d2 // 2 ** (b - 1)
                        assert e2 * 2 ** (b - 1) == d2
                        D0 = e2 - d1
                        D1 = 2 * d1 - e2
                        if D0 == 0 or D1 == 0:
                            continue
                        g = math.gcd(D0, D1)
                        pr = (D0 // g, D1 // g) if D0 > 0 else (-D0 // g, -D1 // g)
                        if pr in polys:
                            continue
                        polys.add(pr)
                        z = F(-pr[1], pr[0])
                        if z > 1:
                            roots.add(z)
    out = sorted(roots)
    stats = {"n_determinants": n_total, "n_mixed_minors_evaluated": n_eval, "n_distinct_polys": len(polys),
             "n_irreducible_factors": len(polys), "n_roots": len(out), "seconds": time.time() - t0,
             "note": "every poly is z^(b-1)(D0 z + D1): distinct linear factors = distinct polys"}
    return (out, stats) if return_stats else out


def _k_in(lo, hi):
    """Rational k with lo < k^2 < hi (hi None: unbounded), exact check."""
    lo = F(lo)
    if hi is None:
        k = F(math.isqrt(math.ceil(lo)) + 1)
        assert k * k > lo
        return k
    hi = F(hi)
    mid = (lo + hi) / 2
    for s in range(0, 2000, 3):
        q = 1 << s
        k = F(math.isqrt(int(mid * q * q)), q)
        if lo < k * k < hi:
            return k
    raise ArithmeticError("gap too narrow")


def gap_point(roots, i):
    """Rational k with k^2 strictly inside gap i (gap 0 = (1, r_0), last gap = (r_last, inf))."""
    lo = F(1) if i == 0 else roots[i - 1]
    hi = roots[i] if i < len(roots) else None
    return _k_in(lo, hi)


# ---------------------------------------------------------------- oracle interface


@dataclass
class OracleAnswer:
    """Answer of a box oracle.  feasible: the decision.  Optional certificates (None = not supplied):
    YES: `columns` (list of frozensets of corner indices, each weakly reachable at W) and `masses`
    (Fractions >= 0) with lo <= sum m_S 1_S <= hi;  NO: `lam` (Farkas vector over the corners, see
    `check_farkas`)."""
    feasible: bool
    columns: Optional[list] = None
    masses: Optional[list] = None
    lam: Optional[list] = None


BoxOracle = Callable[[list, list, list], "bool | OracleAnswer"]


def as_answer(res):
    return res if isinstance(res, OracleAnswer) else OracleAnswer(bool(res))


def box_bounds(T, y):
    """lo, hi over the 2T corners (L_1..L_T, U_1..U_T) for BOX: w(L_t) >= y_t >= w(U_t) (w >= 0)."""
    y = [F(v) for v in y]
    lo = y + [F(0)] * T
    hi = [INF] * T + y
    return lo, hi


def corners(P, k):
    """Exact corners (P/k, P k): lower T points, then upper T points."""
    k = F(k)
    return [tuple(F(c) / k for c in p) for p in P] + [tuple(F(c) * k for c in p) for p in P]


def _cone_lp(columns, lo, hi):
    """Exact: m >= 0 with lo_r <= sum_S m_S [r in S] <= hi_r (finite bounds only).  Returns
    (masses, None) or (None, lam) with lam = Farkas vector (see `check_farkas`)."""
    n = len(lo)
    K = len(columns)
    rows, rhs, kinds = [], [], []
    for r in range(n):
        if not math.isinf(float(lo[r])) and F(lo[r]) > 0:
            rows.append(r)
            rhs.append(F(lo[r]))
            kinds.append("lo")
        if not math.isinf(float(hi[r])):
            rows.append(r)
            rhs.append(F(hi[r]))
            kinds.append("hi")
    A = []
    nsl = len(rows)
    for i, (r, kd) in enumerate(zip(rows, kinds)):
        A.append([F(int(r in S)) for S in columns] + [F((-1 if kd == "lo" else 1) * int(i == j)) for j in range(nsl)])
    res = simplex(A, rhs)
    if res["status"] == "optimal":
        return list(res["x"][:K]), None
    pi = res["pi"]
    lam = [F(0)] * n
    for i, r in enumerate(rows):
        lam[r] -= pi[i]       # lam = -(pi_lo + pi_hi)
    return None, lam


def check_farkas(columns_or_all, lo, hi, lam):
    """Exact algebra of a NO certificate: u = max(-lam, 0) needs finite lo, v = max(lam, 0) needs
    finite hi, and u.lo - v.hi > 0.  (The remaining condition lam(S) >= 0 over all weakly reachable
    S is checked separately.)"""
    val = F(0)
    for r, lm in enumerate(lam):
        lm = F(lm)
        if lm < 0:
            if math.isinf(float(lo[r])):
                return False
            val += -lm * F(lo[r])
        elif lm > 0:
            if math.isinf(float(hi[r])):
                return False
            val -= lm * F(hi[r])
    return val > 0


def all_reachable_sets(W):
    """All weakly reachable subsets of W, exactly (2^|W| exact checks; tiny instances only)."""
    n = len(W)
    out = []
    for mask in range(1 << n):
        S = frozenset(i for i in range(n) if mask >> i & 1)
        if is_weakly_reachable(W, S):
            out.append(S)
    return out


_BRUTE_CACHE = {}


def oracle_brute(W, lo, hi):
    """Reference oracle for any d: all weakly reachable sets of W by exact enumeration, then an exact
    LP.  Returns an OracleAnswer with exact certificates (masses / Farkas vector).  Tiny |W| only."""
    key = tuple(W)
    if key not in _BRUTE_CACHE:
        if len(_BRUTE_CACHE) > 50:
            _BRUTE_CACHE.clear()
        _BRUTE_CACHE[key] = all_reachable_sets([tuple(w) for w in W])
    cols = [S for S in _BRUTE_CACHE[key] if S]
    masses, lam = _cone_lp(cols, lo, hi)
    if masses is not None:
        keep = [(S, m) for S, m in zip(cols, masses) if m != 0]
        return OracleAnswer(True, [S for S, _ in keep], [m for _, m in keep])
    return OracleAnswer(False, lam=lam)


def oracle_flow(W, lo, hi, certify=True):
    """d = 2 only, BOX form only (lo = (y, 0..), hi = (inf.., y)): box.decide (interior-point flow LP).
    With certify=True also supplies certificates: YES columns/masses (flow decomposition, exact
    masses by `_cone_lp`), NO the Farkas vector of box.refute.  Other bounds: NotImplementedError."""
    from . import box
    n = len(W)
    T = n // 2
    if len(W[0]) != 2:
        raise NotImplementedError("oracle_flow is for d = 2")
    y = [F(v) for v in lo[:T]]
    if not (all(math.isinf(float(h)) for h in hi[:T]) and all(F(v) <= 0 for v in lo[T:])
            and [F(h) for h in hi[T:]] == y):
        raise NotImplementedError("oracle_flow supports the box form only")
    L, U = list(W[:T]), list(W[T:])
    ok = box.decide(L, U, y)
    if not certify:
        return ok
    if ok:
        try:
            sol = box._ipm(box.corners(L, U), y, T)
            cand = [S for S, m in box.sets_and_masses(box.corners(L, U), sol["G"], sol["f"], sol["g"], 1e-9)
                    if is_weakly_reachable(W, S)]
            masses, _ = _cone_lp(cand, lo, hi)
            if masses is not None:
                keep = [(S, m) for S, m in zip(cand, masses) if m != 0]
                return OracleAnswer(True, [S for S, _ in keep], [m for _, m in keep])
        except Exception:
            pass
        return OracleAnswer(True)
    return OracleAnswer(False, lam=box.refute(L, U, y))


# ---------------------------------------------------------------- the algorithm


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


def column_oracle_brute(W, lam):
    """min over weakly reachable S of lam(S), exactly by enumeration (tiny |W|)."""
    return min((sum((F(lam[r]) for r in S), F(0)) for S in all_reachable_sets([tuple(w) for w in W])),
               default=F(0))


def column_oracle_planar(W, lam):
    """d = 2: exact min_S lam(S) = -max_S (-lam)(S) via the longest-path oracle of planar.py."""
    from . import box
    best, _ = box.planar.max_weight([tuple(w) for w in W], [-F(v) for v in lam])
    return -best
