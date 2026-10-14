"""Weighted (zonotope) perturbation radius for weak solvability.

Each year t has penalties kappa[t][i] > 0 for the d normalised prices and kappa0[t] > 0 for the
normalising price.  With u = ln q - ln p the distance is

    d_kappa(q_t, p_t) = min_s max(kappa0 |s|, max_i kappa_i |u_i + s|).

Facts (see README.md, "Weighted formulation"):
  1. {d_kappa <= rho} is the box [-rho/kappa_i, rho/kappa_i] plus the diagonal segment of
     half-length rho/kappa0 (a zonotope).  Its bounding box has half-widths
     a_i = rho (1/kappa_i + 1/kappa0); the corners +-a lie in it, and so does the log-linear path
     theta -> theta v, v_i = 1/kappa_i + 1/kappa0, |theta| <= rho.
  2. Feasibility at rho <=> BOX(L, U, y) with L = p exp(-a), U = p exp(+a) (one oracle call).
  3. A solution can be taken on the path q_t = p_t exp(theta_t v_t), |theta_t| <= rho.
  4. Feasibility is monotone in rho and the feasible set is closed.

Oracle interface as in proj.py: oracle(W, lo, hi) with W = (L_1..L_T, U_1..U_T), bounds from
proj.box_bounds.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from . import proj

# ---------------------------------------------------------------- distance


def wdist(q, p, kappa, kappa0):
    """d_kappa(q, p), exactly up to float rounding.  The function of s is a max of lines
    +-kappa_i (u_i + s), +-kappa0 s, convex piecewise linear, and its minimum is attained at a
    pairwise intersection of two of these lines (or at a point where one line is flat, which does
    not happen since all slopes are nonzero); we evaluate f at all intersections."""
    u = [math.log(float(a)) - math.log(float(b)) for a, b in zip(q, p)]
    lines = []  # (slope, intercept)
    for ui, ki in zip(u, kappa):
        lines += [(ki, ki * ui), (-ki, -ki * ui)]
    lines += [(kappa0, 0.0), (-kappa0, 0.0)]

    def f(s):
        return max(a * s + b for a, b in lines)

    best = float("inf")
    for i in range(len(lines)):
        for j in range(i + 1, len(lines)):
            (a1, b1), (a2, b2) = lines[i], lines[j]
            if a1 != a2:
                best = min(best, f((b2 - b1) / (a1 - a2)))
    return best


def path_vector(kappa_t, kappa0_t):
    """v_i = 1/kappa_i + 1/kappa0: half-widths of the bounding box per unit rho."""
    return [1.0 / k + 1.0 / kappa0_t for k in kappa_t]


# ---------------------------------------------------------------- safe rounding of corners


def _round(v, up):
    """Rational c with c >= v (up=True) or c <= v (up=False), v an mpmath number; checked with
    the high-precision value.  Denominator <= 10^10."""
    import mpmath as mp
    c = F(float(v)).limit_denominator(10**9)
    step = F(1, 10**10)
    for _ in range(100):
        cm = mp.mpf(c.numerator) / c.denominator
        if (cm >= v) if up else (cm <= v):
            return c
        c += step if up else -step
    raise ArithmeticError("rounding failed")


def wcorners(P, kappa, kappa0, rho, inner=True):
    """Exact rational corners W = (L_1..L_T, U_1..U_T), L = p exp(-a), U = p exp(a),
    a_i = rho (1/kappa_i + 1/kappa0).  The floats rho, kappa are taken as exact numbers.
    inner=True: the box [L, U] is contained in the true box (use for YES); inner=False: contains
    it (use for NO).  rho = 0 gives exactly P."""
    import mpmath as mp
    mp.mp.dps = 40
    Ls, Us = [], []
    for t, p in enumerate(P):
        lo_t, hi_t = [], []
        for i, pi in enumerate(p):
            pi = F(pi)
            if rho == 0:
                lo_t.append(pi)
                hi_t.append(pi)
                continue
            a = mp.mpf(rho) * (1 / mp.mpf(kappa[t][i]) + 1 / mp.mpf(kappa0[t]))
            pm = mp.mpf(pi.numerator) / pi.denominator
            lo_t.append(_round(pm * mp.exp(-a), up=inner))
            hi_t.append(_round(pm * mp.exp(a), up=not inner))
        Ls.append(tuple(lo_t))
        Us.append(tuple(hi_t))
    return Ls + Us


# ---------------------------------------------------------------- bisection


def least_wradius(P, y, kappa, kappa0, oracle, tol=1e-6, rho_hi=1.0):
    """Bracket the least rho by bisection.  At each rho: inner box YES -> feasible; else outer box
    NO -> infeasible; if inner says NO and outer says YES (rho within rounding of a breakpoint)
    rho is treated as YES and noted.  Returns (lo, hi, calls, answers): infeasible at lo (or
    lo = 0 feasible), feasible at hi; answers = list of (rho, 'YES'|'NO'|'AMBIG')."""
    T = len(P)
    lo_b, hi_b = proj.box_bounds(T, [F(v) for v in y])
    calls = [0]
    answers = []

    def feasible(rho):
        calls[0] += 1
        if proj.as_answer(oracle(wcorners(P, kappa, kappa0, rho, True), lo_b, hi_b)).feasible:
            answers.append((rho, "YES"))
            return True
        if rho == 0:
            answers.append((rho, "NO"))
            return False
        calls[0] += 1
        if proj.as_answer(oracle(wcorners(P, kappa, kappa0, rho, False), lo_b, hi_b)).feasible:
            answers.append((rho, "AMBIG"))
            return True
        answers.append((rho, "NO"))
        return False

    if feasible(0.0):
        return 0.0, 0.0, calls[0], answers
    a, b = 0.0, rho_hi
    while not feasible(b):
        a, b = b, 2 * b
    while b - a > tol:
        mid = (a + b) / 2
        if feasible(mid):
            b = mid
        else:
            a = mid
    return a, b, calls[0], answers


def solve_at(P, y, kappa, kappa0, rho, oracle):
    """Oracle answer at rho (inner box, else outer box).  Returns (answer, inner_flag)."""
    T = len(P)
    lo_b, hi_b = proj.box_bounds(T, [F(v) for v in y])
    ans = proj.as_answer(oracle(wcorners(P, kappa, kappa0, rho, True), lo_b, hi_b))
    if ans.feasible:
        return ans, True
    return proj.as_answer(oracle(wcorners(P, kappa, kappa0, rho, False), lo_b, hi_b)), False


# ---------------------------------------------------------------- witness on the log-linear path


def _in_K(R, x, tol=1e-12):
    """x in conv(R) + R^d_{>=0}, float LP.  R: array (m, d); empty R -> False."""
    m = len(R)
    if m == 0:
        return False
    res = linprog(np.zeros(m), A_ub=R.T, b_ub=x + tol, A_eq=np.ones((1, m)), b_eq=[1.0],
                  bounds=[(0, None)] * m, method="highs")
    return res.status == 0


def _theta_star(R, p, v, rho, iters=45):
    """min{theta in [-rho, rho] : p exp(theta v) in K}; +inf if not even at theta = rho,
    -rho if already at -rho."""
    def pt(th):
        return p * np.exp(th * v)
    if not _in_K(R, pt(rho)):
        return float("inf")
    if _in_K(R, pt(-rho)):
        return -rho
    a, b = -rho, rho
    for _ in range(iters):
        mid = (a + b) / 2
        if _in_K(R, pt(mid)):
            b = mid
        else:
            a = mid
    return a


def wwitness(P, y, kappa, kappa0, rho, columns, masses, inner=True, check_oracle=None, delta=1e-8):
    """Box-theorem construction on the log-linear path.  columns / masses: oracle answer at the
    corners wcorners(.., rho, inner).  For each set S and t, theta*(S,t) = min{theta in [-rho,rho]
    : p_t exp(theta v_t) in K_S}, K_S = conv{W_r : r not in S} + R^d_+; hi_t(theta) =
    sum m_S [theta <= theta*(S,t)]; theta_t = max{theta : hi_t(theta) >= y_t}; Q_t = p_t
    exp(theta_t v_t).  Float LPs (tol 1e-10 in theta).  Returns dict with Q (floats), theta,
    maxdist (max_t wdist(Q_t, p_t)), feasible.

    Check.  Q lies exactly on the boundaries of the sets K_S (ties), and a tie cannot be resolved
    in floating point: a plain weak-solvability test at the float Q fails by a macroscopic amount
    (the tied mass is forced in or out).  So `feasible` is the BOX test with corners
    Q exp(-+delta) (default delta = 1e-8, via check_oracle, default proj.oracle_flow, d = 2): y is
    weakly solvable at some price within relative distance delta of Q."""
    T = len(P)
    W = wcorners(P, kappa, kappa0, rho, inner)
    Wf = np.array([[float(c) for c in w] for w in W])
    Pf = np.array([[float(c) for c in p] for p in P])
    cols = [frozenset(S) for S in columns]
    ms = [float(m) for m in masses]
    thetas, Q = [], []
    for t in range(T):
        v = np.array(path_vector(kappa[t], kappa0[t]))
        ths = []
        for S in cols:
            R = Wf[[r for r in range(2 * T) if r not in S]]
            ths.append(_theta_star(R, Pf[t], v, rho))
        yt = float(y[t])
        cands = sorted({th for th in ths if -rho <= th <= rho} | {rho, -rho}, reverse=True)
        chosen = None
        for c in cands:
            if sum(m for m, th in zip(ms, ths) if c <= th) >= yt * (1 - 1e-9):
                chosen = c
                break
        if chosen is None:
            chosen = -rho
        thetas.append(chosen)
        Q.append(Pf[t] * np.exp(chosen * v))
    maxd = max(wdist(Q[t], Pf[t], kappa[t], kappa0[t]) for t in range(T))
    oracle = check_oracle or (lambda W_, lo_, hi_: proj.oracle_flow(W_, lo_, hi_, certify=False))
    Wchk = ([tuple(F(float(c * math.exp(-delta))) for c in q) for q in Q]
            + [tuple(F(float(c * math.exp(delta))) for c in q) for q in Q])
    lo_b, hi_b = proj.box_bounds(T, [F(v) for v in y])
    ok = proj.as_answer(oracle(Wchk, lo_b, hi_b)).feasible
    return {"Q": [tuple(float(c) for c in q) for q in Q], "theta": thetas, "maxdist": maxd,
            "feasible": bool(ok)}


# ---------------------------------------------------------------- default weights


BASE_PENALTY = {"K": 1.0, "L": 3.0, "II": 3.0, "GO": 4.0}


def default_weights(years, d, names, base=None, year_factor=True):
    """Penalties (kappa, kappa0) for the years `years`, the d normalised prices and the
    normalising price.  `names` lists d + 1 price names, the LAST one being the normalising price
    (US data, d = 2: ["K", "L", "II"]).

    Rule: kappa = base[name] * tau_t, tau_t = 0.5 + 0.5 (t - t0)/(T - 1) (oldest year pays half).
    A larger penalty means the price is trusted more, so moving it costs more: the imputed capital
    rental price K (least reliable) is cheapest to move; labour compensation per hour L and the
    intermediate-input price II are well measured; the output price GO (when it is the normalising
    price at d >= 3) is the best measured.  Older years carry less reliable deflators and are
    cheaper to move.  The final US calibration (README, table) kept the suggested base
    K = 1, L = 3, II = 3, GO = 4 with the year factor.

    Returns kappa (T lists of d floats), kappa0 (T floats)."""
    base = dict(BASE_PENALTY if base is None else base)
    assert len(names) == d + 1
    T = len(years)
    order = sorted(range(T), key=lambda t: years[t])
    rank = {t: r for r, t in enumerate(order)}
    kappa, kappa0 = [], []
    for t in range(T):
        tau = (0.5 + 0.5 * rank[t] / (T - 1)) if (year_factor and T > 1) else 1.0
        kappa.append([base[n] * tau for n in names[:d]])
        kappa0.append(base[names[d]] * tau)
    return kappa, kappa0
