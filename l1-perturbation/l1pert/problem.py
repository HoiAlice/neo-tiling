"""The problem, its cost, exact corners and certified solutions.

Prices P (rational, T points of R^d_{>0}), outputs y >= 0, weights c[t][i] > 0, 1 <= p <= inf.
Cost of new prices Q: one weighted l_p norm of the whole vector of deviations,
    C_p(Q) = || c o dev(Q) ||_p,   dev = ln Q - ln P (metric "log")  or  Q / P - 1 (metric "rel").
Half-widths (alpha, beta) >= 0 give the box [P g(-alpha), P g(beta)], g = exp ("log") or
g(z) = 1 + z ("rel", alpha < 1), of cost ||c o (alpha + beta)||_p; a cost is achievable by some Q iff
it is achievable by a box passing ONE box query (Lean `exists_weakSolvable_iff_boxFeasible_lp`,
`_linf`, `_rel_lp`).  In "rel" the corners are linear in the half-widths: the master's cover rows are exact.
"""

from __future__ import annotations

import math
from fractions import Fraction as F

import numpy as np

from perturb import proj
from perturb.exact_oracle import oracle_exact
from perturb.onesided import _gamma_linear


def _short(v, up):
    """A short rational c >= v (up) or c <= v, v > 0, within relative 10^-12 of v."""
    e = F(10) ** (12 - math.floor(math.log10(float(v))))
    n = v * e
    return F(math.ceil(n) if up else math.floor(n)) / e


class Problem:
    AMAX = 1 - 1e-9                                    # "rel": lower half-widths stay below 1

    def __init__(self, P, y, c=None, p=1.0, metric="log"):
        self.P = [tuple(F(v) for v in q) for q in P]
        self.y = [F(v) for v in y]
        self.T, self.d = len(P), len(P[0])
        self.c = np.array(c, dtype=float) if c is not None else np.ones((self.T, self.d))
        self.p, self.metric = float(p), metric
        self.pi = np.array([[math.log(float(v)) for v in q] for q in self.P])
        self.lo, self.hi = proj.box_bounds(self.T, self.y)
        self.calls = 0

    # ------------------------------------------------------------ cost

    def norm(self, X):
        """|| c o X ||_p for a T x d matrix X."""
        v = self.c * np.abs(np.asarray(X, dtype=float))
        if math.isinf(self.p):
            return float(v.max())
        if self.p == 1:
            return float(v.sum())
        m = v.max()
        return 0.0 if m == 0 else float(m * ((v / m) ** self.p).sum() ** (1 / self.p))

    def dev(self, Q):
        r = [[F(Q[t][i]) / self.P[t][i] for i in range(self.d)] for t in range(self.T)]
        return np.array([[math.log(float(v)) if self.metric == "log" else float(v - 1) for v in q] for q in r])

    def cost(self, Q):
        """C_p of rational prices Q (float value of exact ratios)."""
        return self.norm(self.dev(Q))

    def zmax(self, UB):
        """Bounds of the half-widths (alpha block, beta block) for boxes of cost <= UB."""
        z = (UB / self.c).ravel() * (1 + 1e-9) + 1e-12
        return np.concatenate([np.minimum(z, self.AMAX) if self.metric == "rel" else z, z])

    # ------------------------------------------------------------ oracle

    def verified(self, Q):
        """Is y weakly solvable at the rational Q?  The oracle only PROPOSES a certificate (weakly
        reachable sets and masses); it is accepted only after an independent exact check: every set
        weakly reachable (exact LP per index, proj.is_weakly_reachable) and sum m_S 1_S = y exactly."""
        self.calls += 1
        try:
            Q = [tuple(F(v) for v in q) for q in Q]
            ans = proj.as_answer(oracle_exact(Q, self.y, self.y))
            if not ans.feasible or ans.columns is None:
                return False
            if any(m < 0 for m in ans.masses) or not all(proj.is_weakly_reachable(Q, S) for S in ans.columns):
                return False
            return all(sum(m for S, m in zip(ans.columns, ans.masses) if t in S) == self.y[t]
                       for t in range(self.T))
        except Exception:
            return False

    def lift(self, W, lam):
        """The rational box W with every half-width grown by at least lam >= 0 (rational rounding
        outward): "log" multiplies the corners by kappa >= e^lam, "rel" moves them by lam * p (lower
        half-widths capped at AMAX)."""
        T = len(W) // 2
        if self.metric == "log":
            k = F(math.exp(lam)).limit_denominator(10**9) + F(1, 10**9)
            return [tuple(v / k for v in w) for w in W[:T]] + [tuple(v * k for v in w) for w in W[T:]]
        lm = F(lam).limit_denominator(10**9) + F(1, 10**9)
        floor = F(1) - F(self.AMAX)
        return ([tuple(_short(max(v - lm * pv, floor * pv), False) for v, pv in zip(w, self.P[t]))
                 for t, w in enumerate(W[:T])]
                + [tuple(_short(v + lm * pv, True) for v, pv in zip(w, self.P[t])) for t, w in enumerate(W[T:])])

    def box_cost(self, W):
        """An upper bound of C_p over the box W (rounded up): every point u of the box has
        |dev| <= max(alpha, beta) coordinatewise.  A box that passes the query contains a feasible Q
        (Lean `exists_weakSolvable_iff_boxFeasible_lp`), so this is a valid UB."""
        al, be = self.halfwidths(W, shift=1e-12)
        return self.norm(np.maximum(al, be)) * (1 + 1e-12)

    def halfwidths(self, W, shift=-1e-12):
        """Half-widths of a rational box, rounded DOWN (a cut z_j >= value stays valid); shift > 0
        rounds up."""
        T, log = self.T, self.metric == "log"
        lo = [[F(W[t][i]) / self.P[t][i] for i in range(self.d)] for t in range(T)]
        up = [[F(W[T + t][i]) / self.P[t][i] for i in range(self.d)] for t in range(T)]
        al = np.array([[-math.log(float(r)) if log else float(1 - r) for r in q] for q in lo])
        be = np.array([[math.log(float(r)) if log else float(r - 1) for r in q] for q in up])
        sh = lambda x: np.where(x != 0, np.maximum(x + shift, 0.0), 0.0)   # noqa: E731  (a corner = p is exact)
        return sh(al), sh(be)

    def corners_rounded(self, al, be, inner, years=None):
        """Rational corners rounded safely: inner=True gives a box inside the true box (a YES transfers
        to the true box), inner=False a box containing it (a NO transfers).  years: only these years
        (al, be still indexed by all years)."""
        if self.metric == "rel":                       # p (1 - a), p (1 + b), short rationals rounded safely
            def rnd(pv, z, sg, up):                    # p (1 + sg z); z = 0 keeps p exactly
                return pv if z <= 0 else _short(pv * (1 + sg * F(min(z, self.AMAX))), up)
            ys = range(self.T) if years is None else years
            return ([tuple(rnd(pv, float(al[t, i]), -1, inner) for i, pv in enumerate(self.P[t])) for t in ys]
                    + [tuple(rnd(pv, float(be[t, i]), 1, not inner) for i, pv in enumerate(self.P[t])) for t in ys])
        import mpmath as mp
        from perturb import zono
        mp.mp.dps = 40
        Ls, Us = [], []
        for t in (range(self.T) if years is None else years):
            q = self.P[t]
            lo, hi = [], []
            for i, pv in enumerate(q):
                pm = mp.mpf(pv.numerator) / pv.denominator
                a, b = float(al[t, i]), float(be[t, i])
                lo.append(pv if a <= 0 else zono._round(pm * mp.exp(-mp.mpf(a)), up=inner))
                hi.append(pv if b <= 0 else zono._round(pm * mp.exp(mp.mpf(b)), up=not inner))
            Ls.append(tuple(lo))
            Us.append(tuple(hi))
        return Ls + Us

    def box_query(self, W):
        """Exact box query at the corners W: YES with weakly reachable sets and rational masses, or NO
        with an exact Farkas vector (perturb.exact_oracle)."""
        self.calls += 1
        return proj.as_answer(oracle_exact(W, self.lo, self.hi))

    def solution_from_box(self, W, ans):
        """Rational Q in the box W from an exact YES certificate: the construction (C) => (B) of the
        corner theorem on the price-linear segments L_t + theta (U_t - L_t) (exit points are values
        of rational LPs).  Every point of a segment lies in the box, so |dev| <= max(alpha, beta)
        coordinatewise and C_p(Q) <= box_cost(W).  Returns Q if it passes `verified`, else None
        (never raises)."""
        T = self.T
        try:
            Q = []
            for t in range(T):
                a, b = W[t], W[T + t]
                gam = [(lambda g: F(2) if g is None else g)(_gamma_linear(W, set(S), a, b)) for S in ans.columns]
                cands = sorted({F(0), F(1)} | {g for g in gam if g <= 1}, reverse=True)
                th = next(cv for cv in cands
                          if sum(m for m, g in zip(ans.masses, gam) if cv <= g) >= self.y[t])
                Q.append(tuple(F(ai) + th * (F(bi) - F(ai)) for ai, bi in zip(a, b)))
        except Exception:
            return None
        return Q if self.verified(Q) else None

    def trivial(self):
        """A feasible Q: one coordinate of all years equal.  Every set is weakly reachable with the
        witness e_i, so y is weakly solvable (onesided.tex, nonemptiness lemma): feasible by
        construction, no oracle involved.  Returns (cost, Q) at the best value of that coordinate."""
        from scipy.optimize import minimize_scalar
        best = None
        for i in range(self.d):
            x, e = self.pi[:, i], np.eye(self.d)[i]

            def col(s):                                # cost of the common log-value s
                r = np.exp(s - x)
                return self.norm(np.outer(np.log(r) if self.metric == "log" else r - 1, e))
            cands = sorted({F(q[i]) for q in self.P}, key=lambda m: col(math.log(float(m))))[:1]
            if self.p != 1:                            # p = 1: the optimum is a data value
                r = minimize_scalar(col, bounds=(x.min(), x.max()), method="bounded", options={"xatol": 1e-12})
                cands.append(F(math.exp(r.x)).limit_denominator(10**12))
            for m in cands:
                Q = [tuple(m if j == i else self.P[t][j] for j in range(self.d)) for t in range(self.T)]
                if best is None or self.cost(Q) < best[0]:
                    best = (self.cost(Q), Q)
        return best
