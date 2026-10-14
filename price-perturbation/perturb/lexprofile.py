"""Lexicographic profile of per-year radii (weighted formulation, see README "Lexicographic profile").

Year t has penalties kappa[t] (d normalised prices), kappa0[t]; v_t = 1/kappa_t + 1/kappa0_t.  For a
radius vector r = (r_t), feasible(r) <=> BOX with corners L_t = p_t exp(-r_t v_t),
U_t = p_t exp(r_t v_t) (one oracle call) <=> exists theta, |theta_t| <= r_t, with y weakly solvable
at p_t exp(theta_t v_t).  R = {r : feasible(r)} is closed and upward closed.

`profile` computes the lexicographic minimum of the decreasing rearrangement of r over R by stages
(fixed years with fixed radii, free years share a common bound).  The procedure is exact if R is
closed under coordinatewise min (OPEN, see meet_check.py).

Oracle interface as in proj.py: oracle(W, lo, hi), W = (L_1..L_T, U_1..U_T).
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np

from . import proj, zono


class CountingOracle:
    """Wraps an oracle and counts calls."""

    def __init__(self, oracle):
        self.oracle = oracle
        self.count = 0

    def __call__(self, W, lo, hi):
        self.count += 1
        return self.oracle(W, lo, hi)


def rcorners(P, kappa, kappa0, r, inner=True):
    """Exact rational corners W = (L_1..L_T, U_1..U_T) with per-year radii r (r_t = 0 gives P_t)."""
    Ls, Us = [], []
    for t in range(len(P)):
        w = zono.wcorners([P[t]], [kappa[t]], [kappa0[t]], float(r[t]), inner)
        Ls.append(w[0])
        Us.append(w[1])
    return Ls + Us


def rfeasible(P, y, kappa, kappa0, r, oracle):
    """Safe-rounded query.  Inner box YES -> feasible; else outer box NO -> infeasible; inner NO and
    outer YES (within rounding of a breakpoint) -> treated as feasible.
    Returns (feasible, answer, inner_flag); answer is the oracle answer of the deciding query."""
    T = len(P)
    lo_b, hi_b = proj.box_bounds(T, [F(v) for v in y])
    ans = proj.as_answer(oracle(rcorners(P, kappa, kappa0, r, True), lo_b, hi_b))
    if ans.feasible:
        return True, ans, True
    if all(float(x) == 0 for x in r):
        return False, ans, True
    ans2 = proj.as_answer(oracle(rcorners(P, kappa, kappa0, r, False), lo_b, hi_b))
    if ans2.feasible:
        return True, ans2, False
    return False, ans2, False


def least_common(P, y, kappa, kappa0, fixed, oracle, tol=1e-6, hi=None):
    """Least common bound rho (bisection, returns the feasible end, within tol above the least
    value) for the free years (those not in the dict `fixed`: year -> radius), fixed years at their
    radii.  hi: a known feasible bound (default: doubling from 1).  0.0 if feasible at rho = 0."""
    T = len(P)
    free = [t for t in range(T) if t not in fixed]
    if not free:
        return 0.0

    def vec(rho):
        return [fixed[t] if t in fixed else rho for t in range(T)]

    def ok(rho):
        return rfeasible(P, y, kappa, kappa0, vec(rho), oracle)[0]

    if ok(0.0):
        return 0.0
    a = 0.0
    b = hi if hi is not None else 1.0
    while not ok(b):
        a, b = b, 2 * b
    while b - a > tol:
        mid = (a + b) / 2
        if ok(mid):
            b = mid
        else:
            a = mid
    return b


def _lex_less(a, b, tol):
    """a < b lexicographically (sorted decreasing vectors), entries within tol are equal."""
    for x, y_ in zip(a, b):
        if abs(x - y_) > tol:
            return x < y_
    return False


def profile(P, y, kappa, kappa0, oracle, tol=1e-6, eps=None, witness=False,
            witness_oracle=None, delta=None):
    """Lexicographic minimum of the decreasing rearrangement of r over R = {r : feasible(r)}.

    Exact up to the tolerance (like rho*), whether or not R is closed under coordinatewise min.
    State: fixed years F with radii, free years G.
      (1) rho = least common bound of G given the fixed radii (bisection): the next value of the
          lex-min vector.
      (2) B = a set of MINIMUM cardinality in G such that, with r_t = rho on B and
          r_t = rho - eps on G minus B (fixed years as fixed), r is feasible.  Every such B contains
          B0 = {t in G : r_t = rho - eps alone (the other free years at rho) is infeasible}.  If
          G minus B0 is jointly feasible then B = B0 is the unique minimum (no branching).
          Otherwise (the meet property fails on this instance) the supersets B0 + C are searched by
          increasing |C|, and the procedure BRANCHES over all minimum-cardinality feasible B and keeps
          the lexicographically smallest final sorted vector.
      (3) fix B at rho, G := G minus B.  rho = 0 fixes everything remaining at 0.
    Without branching the number of oracle calls is O(T^2 log(1/eps)) (T stages, each a bisection
    and T single-year tests plus one joint test); in the worst case it is exponential.
    eps defaults to 4 tol.  Returns dict: r, stages [{rho, years, branched}], calls,
    meet_violated_at_stage (list of stage numbers where B0 was not jointly feasible), branches
    (number of explored branch points); with witness=True also theta, Q, wfeasible, maxratio
    (BOX check of the witness with delta = 2 tol by default)."""
    T = len(P)
    eps = 4 * tol if eps is None else eps
    co = oracle if isinstance(oracle, CountingOracle) else CountingOracle(oracle)
    info = {"violated": [], "branches": 0}

    def feas(r):
        return rfeasible(P, y, kappa, kappa0, r, co)[0]

    def solve(fixed, hi, stage):
        """Returns (r dict, stages) for the best completion of `fixed`."""
        free = [t for t in range(T) if t not in fixed]
        if not free:
            return dict(fixed), []
        rho = least_common(P, y, kappa, kappa0, fixed, co, tol, hi)
        if rho == 0.0:
            fx = dict(fixed)
            fx.update({t: 0.0 for t in free})
            return fx, [{"rho": 0.0, "years": free, "branched": False}]
        base = [fixed[t] if t in fixed else rho for t in range(T)]
        low = max(rho - eps, 0.0)

        def joint(B):
            return feas([fixed.get(t, rho if t in B else low) for t in range(T)])

        B0 = []
        for t in free:
            rr = list(base)
            rr[t] = low
            if not feas(rr):
                B0.append(t)
        rest = [t for t in free if t not in B0]
        cands = []
        if not rest or joint(set(B0)):
            cands = [set(B0)]
        else:
            info["violated"].append(stage)
            for k in range(1, len(rest) + 1):
                import itertools
                cands = [set(B0) | set(C) for C in itertools.combinations(rest, k)
                         if joint(set(B0) | set(C))]
                if cands:
                    break
        if len(cands) > 1:
            info["branches"] += 1
        best = None
        for B in cands:
            fx = dict(fixed)
            fx.update({t: rho for t in B})
            res, sts = solve(fx, rho, stage + 1)
            st = [{"rho": rho, "years": sorted(B), "branched": len(cands) > 1 or bool(rest and set(B) != set(B0))}] + sts
            key = sorted(res.values(), reverse=True)
            if best is None or _lex_less(key, best[0], 3 * tol):
                best = (key, res, st)
        return best[1], best[2]

    res, stages = solve({}, None, 0)
    r = [res[t] for t in range(T)]
    out = {"r": r, "stages": stages, "calls": co.count, "meet_violated_at_stage": info["violated"],
           "branches": info["branches"]}
    if witness:
        wo = witness_oracle or oracle
        ok, ans, inner = rfeasible(P, y, kappa, kappa0, r, wo)
        out["feasible"] = ok
        if ok and ans.columns is not None:
            out.update(witness_r(P, y, kappa, kappa0, r, ans.columns, ans.masses, inner,
                                 check_oracle=oracle,
                                 delta=2 * tol if delta is None else delta))
        else:
            out["theta"] = None
    return out


# ---------------------------------------------------------------- witness with per-year radii


def _interval(ths, ms, yt, r):
    """[theta-, theta+] cap [-r, r] for hi(th) = sum m [th <= th*] >= y_t and
    lo(th) = sum m [th < th*] <= y_t.  Returns (theta_minus, theta_plus), possibly empty."""
    tol = 1e-9 * max(1.0, yt)
    cands = sorted({th for th in ths if -r <= th <= r} | {r, -r})
    plus = next((c for c in reversed(cands)
                 if sum(m for m, th in zip(ms, ths) if c <= th) >= yt - tol), -r)
    minus = next((c for c in cands
                  if sum(m for m, th in zip(ms, ths) if c < th) <= yt + tol), r)
    return minus, plus


def witness_r(P, y, kappa, kappa0, r, columns, masses, inner=True, check_oracle=None, delta=1e-8,
              mode="nearest"):
    """Per-year-radius version of zono.wwitness.  theta*(S,t) = min{theta in [-r_t, r_t] :
    p_t exp(theta v_t) in K_S}.  The allowed set {theta : lo_t <= y_t <= hi_t} is an interval
    [theta-, theta+]; mode 'nearest': theta_t = point of [theta-, theta+] cap [-r_t, r_t] nearest
    to 0; mode 'max': theta+ (as zono.wwitness).  Returns dict Q, theta, maxratio
    (max_t d_kappa(Q_t, p_t) / r_t over r_t > 0), feasible (BOX check with Q exp(-+delta) via
    check_oracle, default proj.oracle_flow)."""
    T = len(P)
    W = rcorners(P, kappa, kappa0, r, inner)
    Wf = np.array([[float(c) for c in w] for w in W])
    Pf = np.array([[float(c) for c in p] for p in P])
    cols = [frozenset(S) for S in columns]
    ms = [float(m) for m in masses]
    thetas, Q = [], []
    for t in range(T):
        v = np.array(zono.path_vector(kappa[t], kappa0[t]))
        rt = float(r[t])
        ths = []
        for S in cols:
            R = Wf[[i for i in range(2 * T) if i not in S]]
            ths.append(zono._theta_star(R, Pf[t], v, rt))
        minus, plus = _interval(ths, ms, float(y[t]), rt)
        if mode == "max":
            th = plus
        elif minus <= plus:
            th = min(max(0.0, minus), plus)
        else:                      # numerically empty: closest end to 0
            th = min((minus, plus), key=abs)
        th = min(max(th, -rt), rt)
        thetas.append(th)
        Q.append(Pf[t] * np.exp(th * v))
    ratios = [zono.wdist(Q[t], Pf[t], kappa[t], kappa0[t]) / float(r[t]) for t in range(T)
              if float(r[t]) > 0]
    oracle = check_oracle or (lambda W_, lo_, hi_: proj.oracle_flow(W_, lo_, hi_, certify=False))
    Wchk = ([tuple(F(float(c * math.exp(-delta))) for c in q) for q in Q]
            + [tuple(F(float(c * math.exp(delta))) for c in q) for q in Q])
    lo_b, hi_b = proj.box_bounds(T, [F(v) for v in y])
    ok = proj.as_answer(oracle(Wchk, lo_b, hi_b)).feasible
    return {"Q": [tuple(float(c) for c in q) for q in Q], "theta": thetas,
            "maxratio": max(ratios) if ratios else 0.0, "wfeasible": bool(ok)}


def minimal_shift_witness(P, y, kappa, kappa0, rho, oracle, check_oracle=None, delta=1e-8):
    """The cheap variant at a common rho (e.g. rho*): same as zono.wwitness, but theta_t is the
    point of the allowed interval nearest to 0 (instead of the max).  `oracle` must return
    certificates (columns, masses).  Returns the witness_r dict plus 'rho'."""
    ans, inner = zono.solve_at(P, y, kappa, kappa0, rho, oracle)
    if not ans.feasible or ans.columns is None:
        raise ValueError("infeasible at rho, or the oracle gave no certificate")
    out = witness_r(P, y, kappa, kappa0, [rho] * len(P), ans.columns, ans.masses, inner,
                    check_oracle=check_oracle or oracle, delta=delta)
    out["rho"] = rho
    return out
