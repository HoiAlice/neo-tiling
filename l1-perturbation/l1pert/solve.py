"""The exact algorithm: polyblock outer approximation for monotonic optimization (Tuy 2000;
Tuy, Al-Khayyal, Thach 2005, algorithm QA) with a MILP master and combinatorial Benders cuts from the
oracle's NO certificates (Codato, Fischetti 2006).

H = {z : the box of half-widths z passes the box query} is up-closed, the cost f(z) = ||c o z||_p
increasing.  The master MILP (master.py) minimizes f over a relaxation of H; its bound is LB.  The
exact rational part DECIDES, the master only proposes.  UB in the loop is the cost of a box that
passed the query (problem.box_cost); the solution Q is built and checked once, at the end.

Start: the data box (OPT = 0 iff it passes).  Step k, master point v, ||1|| = ||c o 1||_p:
  1. query at v + delta 1, delta = eps UB / (4 ||1||): the optimum lies on ties that the float point v
     meets only approximately; this box covers them.  YES -> UB <= f(v) + delta ||1||.
  2. projection of v along 1 (Tuy 2000, p. 479): boxes v + lam 1, lam from tau = (UB - LB) / (2 ||1||)
     up, bisection, at most proj_steps queries.  YES at hi -> UB.  NO at lo >= tau ->
       * cover cuts: the NO certificates (lam, C) at the boxes of steps 1-2, reduced to minimal cover
         sets (cover_conflict); the master must destroy one cover of each (tex, certificate theorem);
       * polyblock cut on the minimal conflicting years Y (deletion filter): "z_j >= zhat_j for some
         coordinate j of Y", zhat >= v + tau, so v is cut off.  The NO on Y is certified by exhaustive
         enumeration (proj.oracle_brute) when 2|Y| <= cert_max; a NO the enumeration refutes is an
         oracle error and the cut is dropped.
Output: Q (from the best box whose Q passes the independent exact check; else the aligned start,
feasible by the nonemptiness lemma), UB = C_p(Q), LB, status, and `uncertified` = polyblock cuts that
rest on the oracle's unverified NO.  Nothing raises: a failed check only loses information.
Theorem (tex): LB <= OPT_p <= UB, finite stop with UB - LB <= eps UB.
eps must stay above the MILP tolerances (about 1e-6): LB is a solver bound, and below them the gap
cannot close (then only time_limit stops the loop).
"""

from __future__ import annotations

import math
import time
from fractions import Fraction as F

import numpy as np

from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import coo_matrix

from perturb import exact_oracle as eo
from perturb import proj
from perturb.exact_oracle import oracle_exact

from .master import Master


def minimal_conflict(prob, W):
    """A minimal set of years whose box query alone is NO (deletion in blocks, halving)."""
    T = prob.T

    def no(Y):
        WY = [W[t] for t in Y] + [W[T + t] for t in Y]
        return not proj.as_answer(oracle_exact(WY, *proj.box_bounds(len(Y), [prob.y[t] for t in Y]))).feasible
    Y, size = list(range(T)), T // 2
    while size >= 1:
        i = 0
        while i < len(Y):
            if len(Y) - size >= 2 and no(Y[:i] + Y[i + size:]):
                Y = Y[:i] + Y[i + size:]
            else:
                i += size
        size //= 2
    return Y


def cover_conflict(prob, W):
    """Explain a NO at the box W by covers.  The oracle's certificate is (lam, C): lam(S) >= 0 for every
    S that respects the covers C (x_t <= sum_{s in A} x_s), and lam depends on y only.  So the NO holds
    at every box where all covers of C are present.  Returns a minimal such C' (deletion filter) as
    [(t, A, mu)], mu a convex combination of W_A below W_t, or None."""
    ans = proj.as_answer(oracle_exact(W, prob.lo, prob.hi))
    if ans.feasible or ans.lam is None:
        return None
    n, d = len(W), prob.d
    Wq = [tuple(F(c) for c in w) for w in W]
    C = {(t, (s,)) for t in range(n) for s in range(n) if s != t and all(a < b for a, b in zip(Wq[s], Wq[t]))}
    C |= set(eo._HINTS.get((n, d), ()))            # the multi-point covers of this call, verified at W
    den = 1
    for v in ans.lam:
        den = den * F(v).denominator // math.gcd(den, F(v).denominator)
    w = np.array([float(-F(v) * den) for v in ans.lam])

    def holds(Cs):                                 # max_{S respects Cs} -lam(S) <= 0 ?
        cons = []
        if Cs:
            rows, cols, vals = [], [], []
            for k, (t, A) in enumerate(Cs):
                rows += [k] * (1 + len(A)); cols += [t, *A]; vals += [1.0] + [-1.0] * len(A)
            cons = [LinearConstraint(coo_matrix((vals, (rows, cols)), shape=(len(Cs), n)).tocsr(), -np.inf, 0.0)]
        r = milp(-w, constraints=cons, integrality=np.ones(n), bounds=Bounds(0, 1), options={"mip_rel_gap": 0.0})
        return r.x is not None and sum(w[k] for k in range(n) if r.x[k] > 0.5) <= 0
    Cs = sorted(C, key=lambda c: (len(c[1]), c))
    if not holds(Cs):
        return None
    size = max(1, len(Cs) // 2)
    while True:
        i = 0
        while i < len(Cs):
            if holds(Cs[:i] + Cs[i + size:]):
                Cs = Cs[:i] + Cs[i + size:]
            else:
                i += size
        if size == 1:
            break
        size //= 2
    Wf = np.array([[float(c) for c in w_] for w_ in W])
    out = []
    for t, A in Cs:
        k = len(A)
        res = linprog(np.r_[np.zeros(k), -1.0], A_ub=np.hstack([(Wf[list(A)] / Wf[t]).T, np.ones((d, 1))]),
                      b_ub=np.ones(d), A_eq=np.r_[np.ones(k), 0.0][None, :], b_eq=[1.0],
                      bounds=[(0, None)] * k + [(None, None)], method="highs-ds")
        out.append((t, tuple(A), tuple(res.x[:k]) if res.status == 0 else (1.0 / k,) * k))
    return out


def solve(prob, eps=1e-4, time_limit=None, log=None, cert_max=12, inner_max=50, covers=True, proj_steps=3):
    t0, log = time.time(), log or (lambda s: None)
    ub, Q = prob.trivial()
    m, LB, it, status = Master(prob), 0.0, 0, "time_limit"
    unit = prob.norm(np.ones((prob.T, prob.d)))
    stats = {"uncertified": 0, "oracle_errors": 0, "rejected_Q": 0}

    boxes = []                               # (box cost, W, YES certificate), all passed the query

    def improve(W, ans):
        nonlocal ub
        if ans.feasible and ans.columns and prob.box_cost(W) < ub:
            ub = prob.box_cost(W)
            boxes.append((ub, W, ans))

    def cut_from(W):
        """Polyblock cut on the minimal conflicting years Y: "z_j >= zhat_j for some coordinate j of Y"."""
        T, d = prob.T, prob.d
        Y = minimal_conflict(prob, W)
        WY = [W[t] for t in Y] + [W[T + t] for t in Y]
        if 2 * len(Y) <= cert_max:
            if proj.oracle_brute(WY, *proj.box_bounds(len(Y), [prob.y[t] for t in Y])).feasible:
                stats["oracle_errors"] += 1
                return
        else:
            stats["uncertified"] += 1
        al, be = prob.halfwidths(W)
        m.cuts.append({**{t * d + i: float(al[t, i]) for t in Y for i in range(d)},
                       **{T * d + t * d + i: float(be[t, i]) for t in Y for i in range(d)}})

    W0 = prob.P + prob.P                     # the data themselves: OPT = 0 iff this box passes
    improve(W0, prob.box_query(W0))
    if ub <= 1e-12:
        LB, status = 0.0, "optimal"
    while status != "optimal" and (not time_limit or time.time() - t0 < time_limit):
        it += 1
        for _ in range(inner_max):
            sol = m.solve(ub, gap=max(eps / 4, (ub - LB) / (4 * max(ub, 1e-300))))
            if sol is None or not (m.add_violated_pairs(*sol[:2]) or m.add_tangents(*sol[:2], eps / 4)):
                break
        if sol is None:                      # no z of cost < UB passes the cuts
            LB, status = ub, "optimal"
            break
        al, be, bound = sol
        LB = max(LB, bound)
        if ub - LB <= eps * ub + 1e-12:
            status = "optimal"
            break
        Bout = prob.corners_rounded(al, be, False)
        Win = prob.lift(Bout, eps * ub / (4 * unit))   # v + delta 1, delta = eps UB / (4 ||c||): covers ties at v
        ans_in = prob.box_query(Win)
        improve(Win, ans_in)
        if ub - LB <= eps * ub + 1e-12:
            status = "optimal"
            break
        tau = (ub - LB) / (2 * unit)

        def box(lam):
            return prob.lift(Bout, lam)
        lo, hi, Wlo, Whi = None, float(np.max(prob.zmax(ub))), None, None
        lam = tau
        for _ in range(proj_steps):
            W = box(lam)
            ans = prob.box_query(W)
            if ans.feasible:
                hi, Whi, ans_hi = lam, W, ans
            else:
                lo, Wlo = lam, W
            if lo is None and hi <= tau or lo is not None and hi - lo <= tau:
                break
            lam = (lo + hi) / 2 if lo is not None else tau
        if Whi is not None:
            improve(Whi, ans_hi)
        if Wlo is not None:
            if covers:
                for Wc in ([Wlo] if ans_in.feasible else [Win, Wlo]):
                    cc = cover_conflict(prob, Wc)
                    if cc and cc not in m.covers:
                        m.covers.append(cc)
            cut_from(Wlo)
        log(f"it {it}: LB {LB:.6f} UB {ub:.6f} cuts {len(m.cuts)} {stats} {time.time() - t0:.0f}s")
    for b, W, ans in reversed(boxes):        # the solution: from the best box whose Q passes the check
        Qn = prob.solution_from_box(W, ans)
        if Qn is not None:
            Q = Qn
            break
        stats["rejected_Q"] += 1
    ub = prob.cost(Q)                         # <= the box cost
    LB = min(LB, ub)
    if status == "optimal" and ub - LB > eps * ub + 1e-12:
        status = "rejected_Q"                 # the boxes' solutions failed the check: gap not closed
    return {"LB": LB, "UB": ub, "Q": Q, "status": status, "iterations": it, "cuts": len(m.cuts),
            "pairs": len(m.pairs), "covers": len(m.covers), "time": time.time() - t0, **stats}
