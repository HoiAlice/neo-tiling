"""Lexicographic (leximin-style) profile of per-pair half-widths for BOX weak solvability.

Unit = pair (t, i): one symmetric log half-width a_{t,i} >= 0, no weights:
    L^i_t = p^i_t exp(-a_{t,i}),   U^i_t = p^i_t exp(+a_{t,i}).
Feasibility (BOX(L, U, y)) is monotone in every pair.  `wall_profile` computes the lexicographic
minimum of the decreasing rearrangement of the dT half-widths (see the stage description in
wall_profile).  Oracle interface as in proj.py: oracle(W, lo, hi) -> bool | OracleAnswer.

Exactness: exact up to the bisection tolerance.  The number of oracle calls is polynomial when no
branching occurs; in the worst case (the search for a minimum-cardinality blocking set and the
branching over all minimum choices) it is exponential.  Nothing is truncated: the search is
complete.
"""

from __future__ import annotations

import itertools
import math
from fractions import Fraction as F

from . import box, proj, zono


def default_oracle(W, lo, hi):
    return proj.oracle_flow(W, lo, hi, certify=False)


# ---------------------------------------------------------------- boxes with rounding


def box_corners(P, a_minus, a_plus, inner=True):
    """Rational corners (L, U) with L = p exp(-a-), U = p exp(+a+).  inner=True: [L, U] is inside
    the true box (sound YES); inner=False: contains it (sound NO).  a = 0 gives exactly p."""
    import mpmath as mp
    mp.mp.dps = 40
    Ls, Us = [], []
    for t, p in enumerate(P):
        lo_t, hi_t = [], []
        for i, pi in enumerate(p):
            pi = F(pi)
            am, ap = a_minus[t][i], a_plus[t][i]
            pm = mp.mpf(pi.numerator) / pi.denominator
            lo_c = pi if am == 0 else zono._round(pm * mp.exp(-mp.mpf(am)), up=inner)
            hi_c = pi if ap == 0 else zono._round(pm * mp.exp(mp.mpf(ap)), up=not inner)
            lo_t.append(min(lo_c, pi) if inner else lo_c)
            hi_t.append(max(hi_c, pi) if inner else hi_c)
        Ls.append(tuple(lo_t))
        Us.append(tuple(hi_t))
    return Ls, Us


def box_feasible(P, y, a_minus, a_plus, oracle=default_oracle, outer_check=False):
    """BOX(L, U, y) with the walls given by a_minus[t][i], a_plus[t][i] >= 0.  Inner box YES ->
    True.  Inner NO -> False, unless outer_check: then the outer box is also asked and an
    inner-NO / outer-YES (within rounding of a breakpoint) counts as True."""
    T = len(P)
    lo_b, hi_b = proj.box_bounds(T, [F(v) for v in y])
    L, U = box_corners(P, a_minus, a_plus, True)
    if proj.as_answer(oracle(L + U, lo_b, hi_b)).feasible:
        return True
    if not outer_check:
        return False
    L, U = box_corners(P, a_minus, a_plus, False)
    return proj.as_answer(oracle(L + U, lo_b, hi_b)).feasible


# ---------------------------------------------------------------- context


class Ctx:
    def __init__(self, P, y, oracle=default_oracle, tol=1e-6, outer_check=False):
        self.P, self.y = P, y
        self.T, self.d = len(P), len(P[0])
        self.oracle, self.tol, self.outer_check = oracle, tol, outer_check
        self.delta = 5 * tol
        self.calls = 0
        self.cache = {}
        self.walls = [(t, i) for t in range(self.T) for i in range(self.d)]  # pairs (units)
        self.branched = False

    def a_of(self, lam):
        am = [[lam[(t, i)] for i in range(self.d)] for t in range(self.T)]
        return am, [row[:] for row in am]

    def feasible(self, lam):
        key = tuple(lam[w] for w in self.walls)
        if key in self.cache:
            return self.cache[key]
        self.calls += 1
        am, ap = self.a_of(lam)
        r = box_feasible(self.P, self.y, am, ap, self.oracle, self.outer_check)
        self.cache[key] = r
        return r

    def with_levels(self, fixed, free, level, lower=(), low_level=None):
        """Level dict: fixed walls as given, free walls at `level`, walls in `lower` at low_level."""
        lam = dict(fixed)
        for w in free:
            lam[w] = level
        for w in lower:
            lam[w] = low_level
        return lam


def least_common(ctx, fixed, free, hi):
    """Least common level rho for the walls `free` (others at their `fixed` level): bisection on
    [0, hi] (hi must be feasible), tol ctx.tol.  Returns the feasible end of the bracket
    (0.0 if feasible at 0)."""
    def ok(r):
        return ctx.feasible(ctx.with_levels(fixed, free, r))
    if ok(0.0):
        return 0.0
    a, b = 0.0, hi
    while not ok(b):          # should not happen when hi comes from the previous stage
        a, b = b, 2 * b
    while b - a > ctx.tol:
        mid = (a + b) / 2
        if ok(mid):
            b = mid
        else:
            a = mid
    return b


def witness_Q(ctx, lam):
    """Exact box.witness on the inner box of the level dict lam (d = 2): (Q, (L, U))."""
    am, ap = ctx.a_of(lam)
    L, U = box_corners(ctx.P, am, ap, True)
    res = box.witness(L, U, [F(v) for v in ctx.y])
    return (None if res is None else res[0]), (L, U)


def touched_walls(ctx, Q, lam, free):
    """Free walls that the witness Q touches (distance in log < the lowering delta plus
    slack); the others can be lowered while keeping Q in the box."""
    touched = []
    for (t, i) in free:
        q, p = float(Q[t][i]), float(ctx.P[t][i])
        dist = lam[(t, i)] - abs(math.log(q / p))     # distance to the nearer wall
        if dist < ctx.delta + 1e-8:
            touched.append((t, i))
    return touched


def lexkey(vec, tol):
    """Decreasing rearrangement."""
    return sorted(vec, reverse=True)


def lex_less(u, v, tol):
    for a, b in zip(u, v):
        if a < b - tol:
            return True
        if a > b + tol:
            return False
    return False


# ---------------------------------------------------------------- the profile


def _solve(ctx, fixed, free, hi, stages, depth=0):
    """Returns (levels dict over all walls, list of stage records).  Recursive over branches."""
    fixed = dict(fixed)
    free = list(free)
    stages = list(stages)
    while free:
        rho = least_common(ctx, fixed, free, hi)
        if rho <= 0.0:
            for w in free:
                fixed[w] = 0.0
            stages.append({"rho": 0.0, "n": len(free), "B": len(free)})
            return fixed, stages
        low = max(rho - ctx.delta, 0.0)

        def feas_lowered(lowered):
            return ctx.feasible(ctx.with_levels(fixed, free, rho, lowered, low))

        # candidates for B0 (individually blocking pairs): for d = 2 only pairs touched by an exact
        # witness at rho (an untouched pair can be lowered with the witness kept, so it is not
        # individually blocking), else all free pairs.  This restriction is used for B0 ONLY.
        Q = None
        if ctx.d == 2:
            Q, _ = witness_Q(ctx, ctx.with_levels(fixed, free, rho))
        pool = touched_walls(ctx, Q, ctx.with_levels(fixed, free, rho), free) if Q is not None \
            else list(free)
        B0 = [w for w in pool if not feas_lowered([w])]
        rest = [w for w in free if w not in B0]
        # joint test of everything outside B0 lowered
        def joint(Bset):
            return ctx.feasible(ctx.with_levels(
                fixed, free, rho, [w for w in free if w not in Bset], low))
        branches = []
        if joint(set(B0)):
            branches = [list(B0)]
        else:
            # supersets of B0 by increasing size over ALL free pairs outside B0; all minimum
            # choices are kept (complete enumeration, exponential in the worst case)
            ppool = [w for w in free if w not in B0]
            for k in range(1, len(ppool) + 1):
                found = [list(B0) + list(E) for E in itertools.combinations(ppool, k)
                         if joint(set(B0) | set(E))]
                if found:
                    branches = found
                    break
            if not branches:
                raise RuntimeError("no blocking set found: all free pairs at rho should be "
                                   "feasible (inconsistent oracle?)")
        if len(branches) > 1:
            ctx.branched = True
            best = None
            for Bk in branches:
                f2 = dict(fixed)
                for w in Bk:
                    f2[w] = rho
                fr_ = [w for w in free if w not in Bk]
                res = _solve(ctx, f2, fr_, rho, stages + [{"rho": rho, "n": len(free), "B": len(Bk)}],
                             depth + 1)
                if best is None or lex_less(lexkey([res[0][w] for w in ctx.walls], 0),
                                            lexkey([best[0][w] for w in ctx.walls], 0), 2 * ctx.tol):
                    best = res
            return best
        Bk = branches[0]
        stages.append({"rho": rho, "n": len(free), "B": len(Bk), "B0": len(B0)})
        for w in Bk:
            fixed[w] = rho
        free = [w for w in free if w not in Bk]
        hi = rho
    return fixed, stages


def wall_profile(P, y, oracle=default_oracle, tol=1e-6, outer_check=False, hi0=1.0):
    """Lexicographic minimum of the decreasing rearrangement of the pair half-widths a_{t,i}.

    Exact up to the bisection tolerance.  Polynomial number of oracle calls when no branching
    occurs; exponential in the worst case otherwise.  No truncation: complete search.
    Stages: (1) rho(F) = least common level of the free pairs G (bisection, tol); (2)
    minimum-cardinality B in G such that G \\ B can go strictly below rho(F) simultaneously
    (delta = 5 tol): candidates B0 = individually blocking pairs (for d = 2 only pairs touched by an
    exact witness at rho(F) need be tested); joint test; else supersets of B0 by increasing size
    over ALL free pairs outside B0, branching over all minimum-cardinality choices; (3) fix B at
    rho(F), repeat.
    Returns dict: lam (dict pair -> half-width), a_minus, a_plus, stages, calls, branched,
    Q (exact witness on the final box, d = 2), box (L, U)."""
    ctx = Ctx(P, y, oracle, tol, outer_check)
    lam, stages = _solve(ctx, {}, ctx.walls, hi0, [])
    am, ap = ctx.a_of(lam)
    out = {"lam": lam, "a_minus": am, "a_plus": ap, "stages": stages, "calls": ctx.calls,
           "branched": ctx.branched, "ctx": ctx}
    if ctx.d == 2:
        Q, bx = witness_Q(ctx, lam)
        out["Q"], out["box"] = Q, bx
    return out
