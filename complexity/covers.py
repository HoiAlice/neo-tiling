"""Exact minimal strict coverings for small d (rational arithmetic).

t is strictly covered by R iff max_{w in simplex(R)} min_i (p_t^i - sum_r w_r p_r^i) > 0.
A minimal covering set has at most d points (move sum w p down along -e to the boundary of
conv(p_R) + R^d_+ and apply Caratheodory on the face hit), so the family of weakly
reachable sets is determined by the coverings (t, R) with |R| <= d.
"""

from __future__ import annotations

import itertools
from fractions import Fraction


def _solve(A, b):
    """Exact Gaussian elimination; returns the solution or None if singular."""
    n = len(A)
    M = [list(row) + [bb] for row, bb in zip(A, b)]
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col] / M[col][col]
                M[r] = [a - f * c for a, c in zip(M[r], M[col])]
    return [M[i][n] / M[i][i] for i in range(n)]


def cover_margin(P, t, R) -> Fraction:
    """max over w in simplex(R) of min_i (p_t^i - sum w_r p_r^i), exactly."""
    n, d = len(R), len(P[t])
    pt = [Fraction(v) for v in P[t]]
    pr = [[Fraction(v) for v in P[r]] for r in R]
    # unknowns w_1..w_n, s.  equality sum w = 1.  inequalities: w_k >= 0 (n), s <= f_i(w) (d)
    best = None
    ineqs = [("w", k) for k in range(n)] + [("f", i) for i in range(d)]
    for tight in itertools.combinations(ineqs, n):
        A, b = [[Fraction(1)] * n + [Fraction(0)]], [Fraction(1)]
        for kind, k in tight:
            if kind == "w":
                row = [Fraction(0)] * (n + 1)
                row[k] = Fraction(1)
                A.append(row)
                b.append(Fraction(0))
            else:  # s + sum w_r p_r^k = p_t^k
                A.append([pr[r][k] for r in range(n)] + [Fraction(1)])
                b.append(pt[k])
        sol = _solve(A, b)
        if sol is None:
            continue
        w, s = sol[:n], sol[n]
        if any(v < 0 for v in w):
            continue
        if any(s > pt[i] - sum(w[r] * pr[r][i] for r in range(n)) for i in range(d)):
            continue
        if best is None or s > best:
            best = s
    assert best is not None
    return best


def minimal_covers(P, max_size: int | None = None, closed: bool = False):
    """List of (t, R) with R minimal (inclusion) covering t, |R| <= d.
    closed=False: p_t in conv(p_R) + R^d_{++}; closed=True: p_t in conv(p_R) + R^d_+."""
    T, d = len(P), len(P[0])
    k = max_size or d
    covers = []
    for t in range(T):
        others = [r for r in range(T) if r != t]
        found = []
        for size in range(1, k + 1):
            for R in itertools.combinations(others, size):
                if any(set(F) <= set(R) for F in found):
                    continue
                mg = cover_margin(P, t, list(R))
                if mg >= 0 if closed else mg > 0:
                    found.append(R)
        covers += [(t, frozenset(R)) for R in found]
    return covers


def family_from_covers(T, covers):
    """Weakly reachable sets: S with no cover (t, R), t in S, R disjoint from S."""
    fam = []
    for mask in range(1 << T):
        ok = True
        for t, R in covers:
            if mask >> t & 1 and not any(mask >> r & 1 for r in R):
                ok = False
                break
        if ok:
            fam.append(frozenset(i for i in range(T) if mask >> i & 1))
    return fam
