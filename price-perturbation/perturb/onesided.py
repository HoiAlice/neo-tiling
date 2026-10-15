"""One-sided lexicographic profile: a unique least price perturbation with polynomially many oracle calls.

Year t moves along its log-linear path q_t = p_t exp(theta_t v_t), v_t = 1/kappa_t + 1/kappa0_t
(zono.py); on the path d_kappa(q_t, p_t) = |theta_t|.  The units are the 2T half-axes
u = (t, -1), (t, +1) with lengths alpha_t, beta_t >= 0:  theta_t in [-alpha_t, beta_t].
feasible(alpha, beta) <=> BOX with corners L_t = p_t exp(-alpha_t v_t), U_t = p_t exp(beta_t v_t)
(one oracle call, box theorem); the feasible set is closed and upward closed, and it is never empty
(aligning the first coordinates of all q_t makes every set weakly reachable).

`profile` computes the lexicographic minimum of the decreasing rearrangement of (alpha, beta) by
stages, WITHOUT branching:
  (1) lam = least common level of the free units (bisection between 0 and the previous level);
  (2) B0 = free units that cannot go to lam - eps alone (the other free units at lam), found by
      splitting: a group that goes down jointly contains no unit of B0;
  (3) if the free units outside B0 cannot go down jointly (a tie: several alternative blocking sets
      at the same level), units are added to B in the fixed priority order `order` until they can
      (tie-break; reported in `ties`);
  (4) B is fixed at lam.
After a tie, a final pass lowers (bisection) every unit that is not blocking, in priority order.
Without ties the result is the lexicographic minimum, and it is unique.  After a tie it is a
Pareto-minimal element of the feasible set, not necessarily the lexicographic minimum.
Every unit ends at 0 or blocking (cannot be lowered alone), and blocking survives later stages by
monotonicity.  A blocking beta_t > 0 forces theta_t = beta_t for every feasible theta, a blocking
alpha_t > 0 forces theta_t = -alpha_t; both cannot block.  So the profile determines Q uniquely:
theta_t = beta_t, -alpha_t or 0.  Oracle calls: at most 2T stages, each a bisection
(O(log(lam/tol)) calls) and O(T) single-unit tests:  O(T^2 + T log(1/tol)) calls.

Oracle interface as in proj.py: oracle(W, lo, hi), W = (L_1..L_T, U_1..U_T).
"""

from __future__ import annotations

from fractions import Fraction as F

import numpy as np

from . import proj, zono
from .lexprofile import CountingOracle


def icorners(P, kappa, kappa0, lo, hi, inner=True):
    """Exact rational corners for the theta-intervals [lo_t, hi_t] (lo_t <= hi_t, any signs):
    L_t = p_t exp(lo_t v_t), U_t = p_t exp(hi_t v_t), rounded inwards (inner=True) or outwards."""
    Ls, Us = [], []
    for t in range(len(P)):
        Ls.append(zono.wcorners([P[t]], [kappa[t]], [kappa0[t]], -float(lo[t]), inner)[0])
        Us.append(zono.wcorners([P[t]], [kappa[t]], [kappa0[t]], float(hi[t]), inner)[1])
    return Ls + Us


def ifeasible(P, y, kappa, kappa0, lo, hi, oracle, outer=True):
    """Safe-rounded query for the theta-box [lo, hi]: inner YES -> True; else outer NO -> False;
    inner NO and outer YES (within rounding of a breakpoint) -> True, as in lexprofile.rfeasible.
    outer=False: inner answer only (one call; a wrong NO is possible only within the corner
    rounding, ~1e-9 in theta, far below the tolerances used)."""
    lo_b, hi_b = proj.box_bounds(len(P), [F(v) for v in y])
    if proj.as_answer(oracle(icorners(P, kappa, kappa0, lo, hi, True), lo_b, hi_b)).feasible:
        return True
    if not outer or all(float(a) == 0 and float(b) == 0 for a, b in zip(lo, hi)):
        return False
    return proj.as_answer(oracle(icorners(P, kappa, kappa0, lo, hi, False), lo_b, hi_b)).feasible


def units(T):
    """Units (t, s), s = -1 for alpha_t (downward half-axis), +1 for beta_t."""
    return [(t, s) for t in range(T) for s in (-1, 1)]


def profile(P, y, kappa, kappa0, oracle, tol=1e-6, eps=None, order=None, check=True, outer=False,
            log=None):
    """One-sided lexicographic profile (module docstring).  order: priority of the units for the
    tie-break (default: units(T) order).  eps defaults to 4 tol.  outer: also ask the outer box
    after an inner NO in the stage queries (off by default, see ifeasible; the final 'verified'
    check always uses both boxes).  log: optional callable receiving one progress line per stage.
    Returns dict: alpha, beta, theta, Q (floats), stages [{lam, units, tie}], ties (number of
    stages with a tie-break), calls; with check=True also 'verified': the theta-box
    [theta - 2 eps, theta + 2 eps] is feasible, and 'tight': every nonzero unit cannot be lowered
    by eps alone, and 'both': years with alpha_t > 0 and beta_t > 0 (must be empty)."""
    T = len(P)
    eps = 4 * tol if eps is None else eps
    co = oracle if isinstance(oracle, CountingOracle) else CountingOracle(oracle)
    order = list(order) if order is not None else units(T)
    val = {}                                   # fixed units -> length

    def feas(r):
        lo = [-r[(t, -1)] for t in range(T)]
        hi = [r[(t, 1)] for t in range(T)]
        return ifeasible(P, y, kappa, kappa0, lo, hi, co, outer=outer)

    def vec(lam, low=None, lowered=()):
        r = {}
        for u in units(T):
            if u in val:
                r[u] = val[u]
            else:
                r[u] = low if (low is not None and u in lowered) else lam
        return r

    stages = []
    ties = 0
    prev = None
    while len(val) < 2 * T:
        free = [u for u in order if u not in val]
        if feas(vec(0.0)):
            lam = 0.0
        else:
            a = 0.0
            b = prev if prev is not None else 1.0
            while prev is None and not feas(vec(b)):
                a, b = b, 2 * b
            while b - a > tol:
                mid = (a + b) / 2
                if feas(vec(mid)):
                    b = mid
                else:
                    a = mid
            lam = b
        if lam == 0.0:
            val.update({u: 0.0 for u in free})
            stages.append({"lam": 0.0, "units": free, "tie": False})
            break
        low = max(lam - eps, 0.0)

        def blocking(group):
            """Units of `group` that cannot go down alone.  A group that goes down jointly has no
            such unit (upward closedness), so splitting finds k blocking units in O(k log |G|)."""
            if feas(vec(lam, low, set(group))):
                return []
            if len(group) == 1:
                return list(group)
            h = len(group) // 2
            return blocking(group[:h]) + blocking(group[h:])

        h = len(free) // 2                     # all free units jointly: infeasible since lam is least
        B = blocking(free[:h]) + blocking(free[h:]) if len(free) > 1 else list(free)
        rest = [u for u in free if u not in B]
        tie = False
        if rest and not feas(vec(lam, low, set(rest))):
            tie = True
            ties += 1
            for u in rest:                     # greedy tie-break in priority order
                B.append(u)
                rest_u = [x for x in rest if x not in B]
                if not rest_u or feas(vec(lam, low, set(rest_u))):
                    break
        if not B:                              # cannot happen for an exact oracle: lam is least
            B = [free[0]]
            tie = True
            ties += 1
        val.update({u: lam for u in B})
        stages.append({"lam": lam, "units": B, "tie": tie})
        if log:
            log(f"stage {len(stages)}: lam {lam:.6f}, fixed {B}, free {len(free) - len(B)}, "
                f"calls {co.count}")
        prev = lam

    if ties:                                   # tighten: units added by the tie-break need not block
        for u in order:
            if val[u] == 0.0:
                continue
            r = {x: val[x] for x in units(T)}
            r[u] = max(val[u] - eps, 0.0)
            if not feas(r):
                continue
            a, b = 0.0, val[u]
            r[u] = 0.0
            if feas(r):
                b = 0.0
            while b - a > tol:
                r[u] = (a + b) / 2
                if feas(r):
                    b = r[u]
                else:
                    a = r[u]
            val[u] = b

    alpha = [val[(t, -1)] for t in range(T)]
    beta = [val[(t, 1)] for t in range(T)]
    theta = [beta[t] if beta[t] > 0 else -alpha[t] for t in range(T)]
    Pf = [np.array([float(c) for c in p]) for p in P]
    Q = [tuple(float(c) for c in Pf[t] * np.exp(theta[t] * np.array(zono.path_vector(kappa[t], kappa0[t]))))
         for t in range(T)]
    out = {"alpha": alpha, "beta": beta, "theta": theta, "Q": Q, "stages": stages, "ties": ties,
           "both": [t for t in range(T) if alpha[t] > 0 and beta[t] > 0]}
    if check:
        out["verified"] = ifeasible(P, y, kappa, kappa0, [th - 2 * eps for th in theta],
                                    [th + 2 * eps for th in theta], co)
        r = {u: val[u] for u in units(T)}
        tight = True
        for u in units(T):
            if r[u] > 0:
                rr = dict(r)
                rr[u] = max(r[u] - eps, 0.0)
                if feas(rr):
                    tight = False
        out["tight"] = tight
    out["calls"] = co.count
    return out


def _gamma_linear(W, S, a, b):
    """Exact min{theta in [0, 1] : a + theta (b - a) in conv{W_r : r not in S} + R^d_+}; None if
    not even at theta = 1 (or the complement is empty)."""
    d = len(a)
    rest = [r for r in range(len(W)) if r not in S]
    if not rest:
        return None
    k = len(rest)
    rows = []                  # sum lam W_r + sl - theta (b - a) = a ; sum lam = 1 ; theta + u = 1
    for i in range(d):
        rows.append([F(W[r][i]) for r in rest] + [F(int(i == j)) for j in range(d)]
                    + [-(F(b[i]) - F(a[i])), F(0)])
    rows.append([F(1)] * k + [F(0)] * d + [F(0), F(0)])
    rows.append([F(0)] * (k + d) + [F(1), F(1)])
    rhs = [F(a[i]) for i in range(d)] + [F(1), F(1)]
    res = proj.simplex(rows, rhs, [F(0)] * (k + d) + [F(1), F(0)])
    return res["obj"] if res["status"] == "optimal" else None


def rational_solution(P, y, kappa, kappa0, out, oracle, force_linear=False):
    """Rational solution Q from a profile `out`, with an exact certificate.  oracle: exact, plain
    bounds lo = hi = y allowed, certificates (exact_oracle.oracle_exact).
    (1) q_t = the far corner of year t rounded inwards (in the ball: near a vertex the ball is the
        vertex minus the orthant), p_t for years that do not move; checked exactly.
    (2) If (1) fails: exact YES certificate (columns, masses) at the final rational box [L, U], and
        the construction (C) => (B) of the corner theorem along the price-LINEAR segments
        z_t(theta) = L_t + theta (U_t - L_t).  The segment lies in the ball (d/da ln(1 + theta(e^a - 1))
        <= 1), the exit points gamma are values of rational LPs, so Q is rational.
    Returns (Q as Fractions, OracleAnswer at Q, method 'corner' | 'linear')."""
    T = len(P)
    yy = [F(v) for v in y]
    Q = []
    for t in range(T):
        if out["beta"][t] > 0:
            Q.append(zono.wcorners([P[t]], [kappa[t]], [kappa0[t]], out["beta"][t], True)[1])
        elif out["alpha"][t] > 0:
            Q.append(zono.wcorners([P[t]], [kappa[t]], [kappa0[t]], out["alpha"][t], True)[0])
        else:
            Q.append(tuple(F(c) for c in P[t]))
    if not force_linear:
        ans = proj.as_answer(oracle(Q, yy, yy))
        if ans.feasible:
            return Q, ans, "corner"
    W = icorners(P, kappa, kappa0, [-a for a in out["alpha"]], out["beta"], True)
    lo_b, hi_b = proj.box_bounds(T, yy)
    box = proj.as_answer(oracle(W, lo_b, hi_b))
    if not box.feasible or box.columns is None:
        raise ValueError("the final box is not certified feasible")
    Q = []
    for t in range(T):
        a, b = W[t], W[T + t]
        gam = []
        for S in box.columns:
            g = _gamma_linear(W, set(S), a, b)
            gam.append(F(2) if g is None else g)          # 2 = never enters K within [0, 1]
        cands = sorted({F(0), F(1)} | {g for g in gam if g <= 1}, reverse=True)
        th = next(c for c in cands
                  if sum(m for m, g in zip(box.masses, gam) if c <= g) >= yy[t])
        Q.append(tuple(F(ai) + th * (F(bi) - F(ai)) for ai, bi in zip(a, b)))
    return Q, proj.as_answer(oracle(Q, yy, yy)), "linear"


def lex_key(out):
    """Decreasing rearrangement of (alpha, beta)."""
    return sorted(out["alpha"] + out["beta"], reverse=True)
