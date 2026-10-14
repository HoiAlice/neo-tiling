"""Exact least hexagonal perturbation radius at d = 2 (weak solvability).

A 2D price is a normalised 3D price.  The distance between normalised points is the hexagonal
norm in log space, dhat(a, b) = max(|u1|, |u2|, |u1 - u2|), u_i = ln a_i - ln b_i.
rho* = min over Q of max_t dhat(q_t, p_t) subject to "y is weakly solvable at Q".

Facts used (see README.md):
  1. A hexagon of radius rho around ln p_t lies in the square [-rho, rho]^2 and contains its
     diagonal, so the problem equals BOX(p e^{-rho}, p e^{rho}, y) of `box.py`.
  2. The weakly reachable family is invariant under a common scaling, so the corners may be
     (p_t, z p_t) with z = e^{2 rho}.  In the code z = k^2 with k rational.
  3. The chain graph of the corners depends only on signs of coordinate differences and of
     cross products of corner triples.  Each is a polynomial in z of degree <= 2.  Between two
     consecutive roots (> 1) the feasibility of BOX is constant, it is monotone in z, and the
     feasible set is closed.  So rho* = 0 or rho* = (1/2) ln z_k, z_k a breakpoint (a root).

Everything about breakpoints (equality, order, gap points) is decided exactly in rational
arithmetic.  The LP oracle `box.decide` is a float decision; `certify_result` certifies the
answer exactly on both sides (`box.refute`, `box.witness`).
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass, field
from fractions import Fraction as F

import mpmath

import box

mpmath.mp.dps = 150

SMALL_PRIMES = [p for p in range(2, 200) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


# ---------------------------------------------------------------- hexagonal distance


def hexdist(a, b):
    """dhat(a, b) = max(|u1|, |u2|, |u1 - u2|), u = ln a - ln b (float)."""
    u1 = math.log(float(a[0])) - math.log(float(b[0]))
    u2 = math.log(float(a[1])) - math.log(float(b[1]))
    return max(abs(u1), abs(u2), abs(u1 - u2))


def in_hex(Q, P, rho, tol=1e-12):
    """max_t dhat(q_t, p_t) <= rho (float, with a tiny tolerance)."""
    return all(hexdist(q, p) <= rho + tol for q, p in zip(Q, P))


def in_hex_exact(Q, P, k):
    """Exact test for rational k = e^rho: 1/k <= q1/p1, q2/p2, (q1 p2)/(q2 p1) <= k for all t."""
    k = F(k)
    for q, p in zip(Q, P):
        r1, r2 = F(q[0]) / F(p[0]), F(q[1]) / F(p[1])
        if not all(1 / k <= r <= k for r in (r1, r2, r1 / r2)):
            return False
    return True


# ---------------------------------------------------------------- exact algebraic numbers


def sign(x):
    return (x > 0) - (x < 0)


def sign_lin(A, B, D):
    """Sign of A + B sqrt(D), A, B, D rational, D >= 0, exactly."""
    if B == 0 or D == 0:
        return sign(A)
    sa, sb = sign(A), sign(B)
    if sa == 0:
        return sb
    if sa == sb:
        return sa
    d = sign(A * A - B * B * D)         # A and B have opposite signs
    return d if sa > 0 else -d


def sign3(A, B, D1, C, D2):
    """Sign of A + B sqrt(D1) + C sqrt(D2), all rational, D1, D2 >= 0, exactly."""
    if C == 0 or D2 == 0:
        return sign_lin(A, B, D1)
    if B == 0 or D1 == 0:
        return sign_lin(A, C, D2)
    su, sv = sign_lin(A, B, D1), sign(C)
    if su == 0:
        return sv
    if su == sv:
        return su
    # opposite signs: compare u^2 = A^2 + B^2 D1 + 2AB sqrt(D1) with v^2 = C^2 D2
    d = sign_lin(A * A + B * B * D1 - C * C * D2, 2 * A * B, D1)
    return d if su > 0 else -d


class Alg:
    """The real number alpha + beta sqrt(D) (Fractions, D > 0; beta = 0 means rational).
    `key` identifies the number canonically for exact deduplication (see `_poly_roots`)."""

    __slots__ = ("alpha", "beta", "D", "key")

    def __init__(self, alpha, beta=0, D=0, key=None):
        self.alpha, self.beta, self.D = F(alpha), F(beta), F(D)
        if self.beta == 0:
            self.D = F(0)
        self.key = key

    @staticmethod
    def of(x):
        return x if isinstance(x, Alg) else Alg(x)

    def cmp(self, other):
        """-1, 0, 1 for self <, =, > other, decided exactly."""
        o = Alg.of(other)
        return sign3(self.alpha - o.alpha, self.beta, self.D, -o.beta, o.D)

    def __lt__(self, o):
        return self.cmp(o) < 0

    def __le__(self, o):
        return self.cmp(o) <= 0

    def __gt__(self, o):
        return self.cmp(o) > 0

    def __ge__(self, o):
        return self.cmp(o) >= 0

    def __eq__(self, o):
        return self.cmp(o) == 0

    def __hash__(self):
        return hash(self.key) if self.key is not None else hash((self.alpha, self.beta, self.D))

    def is_rational(self):
        return self.beta == 0

    def mpf(self):
        a = mpmath.mpf(self.alpha.numerator) / self.alpha.denominator
        if self.beta == 0:
            return a
        b = mpmath.mpf(self.beta.numerator) / self.beta.denominator
        d = mpmath.mpf(self.D.numerator) / self.D.denominator
        return a + b * mpmath.sqrt(d)

    def __float__(self):
        return float(self.mpf())

    def __repr__(self):
        if self.beta == 0:
            return f"Alg({self.alpha})"
        return f"Alg({self.alpha} + ({self.beta})*sqrt({self.D}))"

    def short(self, digits=12):
        """Human readable form: numbers are shown as floats if too long."""
        def s(x):
            t = str(x)
            return t if len(t) <= 40 else mpmath.nstr(mpmath.mpf(x.numerator) / x.denominator, digits)
        if self.beta == 0:
            return s(self.alpha)
        return f"{s(self.alpha)} + ({s(self.beta)})*sqrt({s(self.D)})"


def _squarefree_small(n):
    """n = s^2 m, removing square factors of small primes only.  Returns (s, m)."""
    s = 1
    for p in SMALL_PRIMES:
        pp = p * p
        if pp > n:
            break
        while n % pp == 0:
            n //= pp
            s *= p
    return s, n


# ---------------------------------------------------------------- polynomials in z


def _padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def _psub(p, q):
    return _padd(p, [-c for c in q])


def _pmul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def _normalize(poly):
    """Primitive integer polynomial with positive leading coefficient, as a tuple (c0, c1, ...);
    None if the polynomial is constant (no roots, or identically zero)."""
    poly = list(poly)
    while poly and poly[-1] == 0:
        poly.pop()
    if len(poly) <= 1:
        return None
    den = 1
    for c in poly:
        den = den * F(c).denominator // math.gcd(den, F(c).denominator)
    ints = [int(F(c) * den) for c in poly]
    g = 0
    for c in ints:
        g = math.gcd(g, c)
    ints = [c // g for c in ints]
    if ints[-1] < 0:
        ints = [-c for c in ints]
    return tuple(ints)


def breakpoint_polynomials(P):
    """The distinct nonconstant polynomials in z (primitive integer tuples (c0, c1, c2)) that
    decide the combinatorics of the corners W(z) = (p_1..p_T, z p_1..z p_T):
    X_a - X_b, Y_a - Y_b for all corner pairs and cross(a, b, q) for all unordered corner triples
    (cross changes only its sign under permutations of the triple)."""
    P = [(F(x), F(y)) for x, y in P]
    T = len(P)
    # coordinate polynomials: p z^0 for c < T, p z^1 for c >= T
    X = [[P[c][0]] if c < T else [F(0), P[c - T][0]] for c in range(2 * T)]
    Y = [[P[c][1]] if c < T else [F(0), P[c - T][1]] for c in range(2 * T)]
    polys = set()

    def add(poly):
        nrm = _normalize(poly)
        if nrm is not None:
            polys.add(nrm)

    for a, b in itertools.combinations(range(2 * T), 2):
        add(_psub(X[a], X[b]))
        add(_psub(Y[a], Y[b]))
    for a, b, q in itertools.combinations(range(2 * T), 3):
        t1 = _pmul(_psub(X[b], X[a]), _psub(Y[q], Y[a]))
        t2 = _pmul(_psub(Y[b], Y[a]), _psub(X[q], X[a]))
        add(_psub(t1, t2))
    return polys


def _poly_roots(poly):
    """Real roots of a primitive integer polynomial of degree 1 or 2 as `Alg` with canonical keys.
    Rational roots: key ('r', value).  Irrational: the polynomial is irreducible over Q, so two
    roots coincide iff they have the same primitive polynomial and the same branch of the square
    root: key ('q', (c0, c1, c2), s)."""
    if len(poly) == 2:
        r = F(-poly[0], poly[1])
        return [Alg(r, key=("r", r))]
    c, b, a = poly
    disc = b * b - 4 * a * c
    if disc < 0:
        return []
    s = math.isqrt(disc)
    if s * s == disc:
        return [Alg(F(-b + e * s, 2 * a), key=("r", F(-b + e * s, 2 * a))) for e in (1, -1)]
    sq, m = _squarefree_small(disc)           # sqrt(disc) = sq sqrt(m)
    return [Alg(F(-b, 2 * a), F(e * sq, 2 * a), m, key=("q", poly, e)) for e in (1, -1)]


def _exact_sort(items):
    """Sort Alg numbers: mpmath pre-sort, then exact insertion sort (cheap if the pre-sort is
    right).  Returns a list in nondecreasing exact order."""
    items = sorted(items, key=lambda x: x.mpf())
    for i in range(1, len(items)):
        j = i
        while j > 0 and items[j - 1].cmp(items[j]) > 0:
            items[j - 1], items[j] = items[j], items[j - 1]
            j -= 1
    return items


def breakpoints(P):
    """All real roots z > 1 of the polynomials of `breakpoint_polynomials(P)`, deduplicated
    exactly and sorted exactly.  List of `Alg`, strictly increasing."""
    roots = {}
    for poly in breakpoint_polynomials(P):
        for r in _poly_roots(poly):
            if r.cmp(1) > 0:
                roots.setdefault(r.key, r)
    out = _exact_sort(list(roots.values()))
    for u, v in zip(out, out[1:]):
        assert u.cmp(v) < 0, "deduplication failed: equal roots with different keys"
    return out


# ---------------------------------------------------------------- gap points


_K_DENOMS = (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128)


def _mpf_to_fraction(x):
    man, exp = x.man_exp
    return F(int(man)) * (F(2) ** exp)


def _k_in(lo, hi):
    """Rational k with lo < k^2 < hi (hi = None: unbounded), exact check."""
    lo = Alg.of(lo)
    if hi is None:
        k = max(2, math.isqrt(int(lo.mpf())) + 2)
        while Alg(k * k).cmp(lo) <= 0:
            k *= 2
        return F(k)
    hi = Alg.of(hi)
    mid = (mpmath.sqrt(lo.mpf()) + mpmath.sqrt(hi.mpf())) / 2
    exact = _mpf_to_fraction(mid)
    for j in _K_DENOMS:
        k = exact.limit_denominator(10 ** j)
        z = Alg(k * k)
        if z.cmp(lo) > 0 and z.cmp(hi) < 0:
            return k
    z = Alg(exact * exact)
    if z.cmp(lo) > 0 and z.cmp(hi) < 0:
        return exact
    raise ArithmeticError("gap too narrow for the working precision")


def gap_point(roots, i):
    """Rational k_i with k_i^2 strictly inside the i-th gap, i = 0..len(roots): gap 0 is
    (1, r_0), gap i is (r_{i-1}, r_i), the last gap is (r_last, infinity)."""
    lo = Alg(1) if i == 0 else roots[i - 1]
    hi = roots[i] if i < len(roots) else None
    return _k_in(lo, hi)


def gap_points(roots):
    """One rational k per gap with k^2 strictly inside the gap (z = k^2 is a rational point of
    the gap; checked exactly)."""
    return [gap_point(roots, i) for i in range(len(roots) + 1)]


# ---------------------------------------------------------------- the algorithm


def log_box(P, k):
    """Exact corners (P/k, P*k)."""
    k = F(k)
    return [(F(a) / k, F(b) / k) for a, b in P], [(F(a) * k, F(b) * k) for a, b in P]


@dataclass
class Result:
    z_star: Alg                  # exact z* = e^{2 rho*} (Alg(1) if rho* = 0)
    rho: float                   # 0.5 ln z*
    gap: int                     # index of the first feasible gap (-1: z = 1 itself is feasible)
    k_below: F                   # rational k just below (k^2 in the previous gap, or 1)
    k_above: F                   # rational k just above (k^2 in the first feasible gap)
    n_calls: int                 # box.decide calls
    n_breakpoints: int
    roots: list = field(repr=False, default_factory=list)
    notes: list = field(default_factory=list)   # contradictions with the facts, if any


def least_radius_exact(P, y, roots=None):
    """rho* = least rho with BOX(P e^{-rho}, P e^{rho}, y), exactly as 0.5 ln z* with z* a
    breakpoint.  O(log #breakpoints) calls of the LP oracle `box.decide`."""
    P = [(F(a), F(b)) for a, b in P]
    if roots is None:
        roots = breakpoints(P)
    m = len(roots)
    calls = [0]
    notes = []
    cache = {}

    def feasible(i):
        """BOX at the rational point of gap i (i = -1: z = 1)."""
        if i not in cache:
            calls[0] += 1
            k = F(1) if i == -1 else gap_point(roots, i)
            cache[i] = box.decide(*log_box(P, k), y)
        return cache[i]

    def kk(i):
        return F(1) if i == -1 else gap_point(roots, i)

    if feasible(-1):
        return Result(Alg(1), 0.0, -1, F(1), F(1), calls[0], m, roots, notes)
    if not feasible(m):
        raise RuntimeError("BOX infeasible even above the last breakpoint")
    lo, hi = -1, m                       # lo infeasible, hi feasible
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if feasible(mid):
            hi = mid
        else:
            lo = mid
    if hi == 0:
        # z = 1 infeasible but the first gap feasible: closedness of the feasible set fails
        notes.append("z=1 infeasible but gap 0 feasible (contradicts closedness; float LP?)")
        z_star = Alg(1)
    else:
        z_star = roots[hi - 1]
    rho = 0.5 * float(mpmath.log(z_star.mpf()))
    return Result(z_star, rho, hi, kk(hi - 1), kk(hi), calls[0], m, roots, notes)


def monotonicity_check(P, y, roots, indices):
    """Evaluate `box.decide` at the gap points with the given indices and return the list of
    (index, feasible).  For testing the monotonicity claim."""
    P = [(F(a), F(b)) for a, b in P]
    return [(i, box.decide(*log_box(P, gap_point(roots, i)), y)) for i in indices]


def certify_result(P, y, res):
    """Exact certificates.  NO at k_below: `box.refute` (exact Farkas vector).  YES at k_above:
    `box.witness` + `box.certify`, and the witness lies in the hexagons of radius ln k_above
    (`in_hex_exact`).  Returns a dict of booleans and the witness."""
    P = [(F(a), F(b)) for a, b in P]
    out = {"no_certified": None, "yes_certified": None, "witness_in_hex": None, "Q": None,
           "rho_above": math.log(res.k_above)}
    if res.gap >= 0:
        lam = box.refute(*log_box(P, res.k_below), y)
        out["no_certified"] = lam is not None
    wit = box.witness(*log_box(P, res.k_above), y)
    if wit is not None:
        Q, cert = wit
        out["Q"] = Q
        out["yes_certified"] = bool(box.certify(Q, y, cert))
        out["witness_in_hex"] = in_hex_exact(Q, P, res.k_above) and in_hex(Q, P, out["rho_above"])
        out["n_sets"] = len(cert)
    else:
        out["yes_certified"] = False
    return out
