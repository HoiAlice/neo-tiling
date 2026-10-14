"""Covering-cut loop for the symmetric perturbation, SCIP only.

    rho(P, y) = min { sum_{t,i} max(q/p, p/q) - 1 : y weakly solvable at Q }

Blocking. t is blocked by R at Q if some xi in the simplex has <xi, q_r - q_t> >= 0 for all
r in R (t does not strictly cover R). A cut is a list C of pairs (t, R) with an integer
refutation w: <w, y> > 0 and every S with w(S) > 0 contains the t and misses the R of some
pair of C. If y is weakly solvable at Q, some pair of every cut is blocked at Q.

Master (MILP + the convex cost g >= a - 1, g >= 1/a - 1, q = p a): the cuts with one binary
per pair. Blocking by one s is exact (q_t^i <= q_s^i for some i); blocking by a larger R is
relaxed by a witness cell: the inequality must hold at the maximizing vertex of a cell of
the partition of t's witness simplex. The master value is a lower bound on rho.

Separation at the master point Q*: column generation for y in cone{1_S : S weakly
reachable at Q*}. Yes: Q* is weakly solvable (exact certificate). No: the duals give w and
a greedy pass picks coverings of Q* that kill every S with w(S) > 0: a new cut. A pair that
the master blocks only through its cell (no witness in the cell at Q*) gets its cell and
the neighbours refined. Upper bounds: repair of the residual family, exact rational snap.
"""

from __future__ import annotations

import itertools
import json
import sys
import time
from fractions import Fraction

import numpy as np
from pyscipopt import Model, quicksum
from scipy.optimize import linprog

from . import certify as C
from .grid import SimplexGrid
from .models import _pricing

TOL = 1e-9


def pi_sym(P, Q) -> Fraction:
    return sum(max(C.F(q) / C.F(p), C.F(p) / C.F(q)) - 1
               for prow, qrow in zip(P, Q) for p, q in zip(prow, qrow))


def _model(time_limit):
    m = Model()
    m.hideOutput()
    m.setParam("limits/time", time_limit)
    m.setParam("limits/memory", 2000)
    m.setParam("limits/gap", 0.0)
    m.setParam("numerics/feastol", 1e-9)
    return m


# ---------------------------------------------------------------- master
def master(P, y, cuts, grids, ub, time_limit):
    T, d = P.shape
    m = _model(time_limit)
    lo, hi = 1 / (1 + ub), 1 + ub
    a = {(t, i): m.addVar(lb=lo, ub=hi) for t in range(T) for i in range(d)}
    g = {k: m.addVar(lb=0, ub=ub) for k in a}
    for k, v in a.items():
        m.addCons(g[k] >= v - 1)
        m.addCons(g[k] >= 1 / v - 1)  # convex on a > 0
    obj = quicksum(g.values())
    m.addCons(obj <= ub)
    m.setObjective(obj)

    def q(t, i):
        return float(P[t, i]) * a[t, i]

    sign, nv, blocked, cellvars = {}, {}, {}, {}

    def beats(t, s, va, vb):
        u = [float(x - z) for x, z in zip(grids[t].vertices[va], grids[t].vertices[vb])]
        top = max(abs(x) for x in u)
        u = [x / top for x in u]
        flip = next(x for x in u if x != 0) < 0
        key = (t, s, tuple(round(-x if flip else x, 12) for x in u))
        if key not in sign:
            x = sign[key] = m.addVar(vtype="B")
            dd = quicksum(key[2][i] * (q(s, i) - q(t, i)) for i in range(d))
            big = sum(abs(key[2][i]) * float(max(P[s, i], P[t, i])) for i in range(d)) * hi
            m.addCons(dd >= -big * (1 - x))
            m.addCons(dd <= big * x)
        return 1 - sign[key] if flip else sign[key]

    def need(t, s, j):
        if (t, s, j) not in nv:
            v = grids[t].vertices[j]
            x = nv[t, s, j] = m.addVar(lb=0, ub=1)
            big = sum(float(v[i]) * float(P[t, i]) for i in range(d)) * hi
            m.addCons(quicksum(float(v[i]) * (q(s, i) - q(t, i)) for i in range(d))
                      >= -big * (1 - x))
        return nv[t, s, j]

    def block(pair):
        if pair in blocked:
            return blocked[pair]
        t, R = pair
        b = blocked[pair] = m.addVar(vtype="B")
        if len(R) == 1:
            (s,) = R
            dl = [m.addVar(vtype="B") for _ in range(d)]
            m.addCons(quicksum(dl) >= b)
            for i in range(d):
                m.addCons(q(t, i) - q(s, i) <= float(P[t, i]) * hi * (1 - dl[i]))
                m.chgVarBranchPriority(dl[i], 10)
            return b
        cells = grids[t].cells
        c = cellvars[pair] = [m.addVar(vtype="B") for _ in cells]
        m.addCons(quicksum(c) == b)
        for s in R:
            for ci, ids in enumerate(cells):
                for j in ids:
                    lose = quicksum(1 - beats(t, s, j, l) for l in ids if l != j)
                    m.addCons(need(t, s, j) >= c[ci] - lose)
                for x1, x2, x3 in itertools.combinations(ids, 3):  # no cyclic signs (d >= 3)
                    cyc = beats(t, s, x1, x2) + beats(t, s, x2, x3) + beats(t, s, x3, x1)
                    m.addCons(cyc >= 1)
                    m.addCons(cyc <= 2)
        return b

    for cut in cuts:
        m.addCons(quicksum(block(p) for p in cut) >= 1)
    m.optimize()
    st, bound = m.getStatus(), (m.getDualbound() if m.getStatus() != "infeasible" else ub)
    if m.getNSols() == 0:
        m.freeProb()
        return dict(Q=None, bound=bound, status=st)
    Q = np.array([[float(P[t, i]) * m.getVal(a[t, i]) for i in range(d)] for t in range(T)])
    active = {p: max(range(len(c)), key=lambda i: m.getVal(c[i]))
              for p, c in cellvars.items() if m.getVal(blocked[p]) > 0.5}
    out = dict(Q=Q, value=m.getObjVal(), bound=bound, status=st, active=active)
    m.freeProb()
    return out


# ---------------------------------------------------------------- separation
def covering(Q, S, t):
    """Support R of a strict covering of t by conv(Q_s, s not in S), or None."""
    T, d = Q.shape
    out = [s for s in range(T) if s not in S]
    if not out:
        return None
    n = len(out)
    c = np.zeros(n + 1)
    c[-1] = -1.0
    A = np.array([[Q[s, i] for s in out] + [1.0] for i in range(d)])
    res = linprog(c, A_ub=A, b_ub=Q[t], A_eq=[[1.0] * n + [0.0]], b_eq=[1.0],
                  bounds=[(0, None)] * n + [(None, None)], method="highs-ds")
    if res.status != 0 or res.x[-1] <= 1e-8:
        return None
    return tuple(sorted(out[j] for j in range(n) if res.x[j] > 1e-12))


def cell_witness(grid, cell, Q, t, R):
    """max over xi in the cell of min_{r in R} <xi, q_r - q_t>."""
    V = np.array([[float(x) for x in grid.vertices[j]] for j in grid.cells[cell]])
    n = len(V)
    c = np.zeros(n + 1)
    c[-1] = -1
    A = [np.concatenate([-(V @ (Q[r] - Q[t])), [1]]) for r in R]
    res = linprog(c, A_ub=A, b_ub=np.zeros(len(R)), A_eq=[[1.0] * n + [0.0]], b_eq=[1.0],
                  bounds=[(0, None)] * n + [(None, None)], method="highs")
    return -res.fun


def refute(Q, y, time_limit):
    """Column generation. ('yes', sets) or ('no', dual) with dual(S) <= 0 on reachable S."""
    T = len(y)
    cols = [frozenset(range(T))]
    while True:
        n = len(cols)
        A = np.array([[1.0 if t in S else 0.0 for S in cols] for t in range(T)]).reshape(T, n)
        res = linprog(np.concatenate([np.zeros(n), np.ones(T)]), A_eq=np.hstack([A, np.eye(T)]),
                      b_eq=y, bounds=[(0, None)] * (n + T), method="highs")
        if res.fun <= TOL * max(1.0, float(max(y))):
            return "yes", [S for S, v in zip(cols, res.x[:n]) if v > 1e-12]
        dual = np.array(res.eqlin.marginals)
        value, S = _pricing(Q, dual, time_limit)
        if value <= TOL or S in cols:
            return "no", dual
        cols.append(S)


def integer_refutation(dual, y):
    w = [round(v * 1e6 / max(np.max(np.abs(dual)), 1e-300)) for v in dual]
    return w if sum(wi * C.F(yi) for wi, yi in zip(w, y)) > 0 else None


def killing_pairs(Q, w, known, time_limit):
    """Pairs of Q such that every S with w(S) > 0 contains the t and misses the R of one."""
    T = len(w)
    m = _model(time_limit)
    x = [m.addVar(vtype="B") for _ in range(T)]
    m.setObjective(quicksum(w[t] * x[t] for t in range(T)), "maximize")
    pairs = []
    while True:
        m.optimize()
        if m.getObjVal() < 0.5:  # integer w: every surviving S has w(S) <= 0
            m.freeProb()
            return pairs
        S = frozenset(t for t in range(T) if m.getVal(x[t]) > 0.5)
        cands = [(t, R) for t, R in known if t in S and not set(R) & S]
        if not cands:
            cands = [(t, R) for t in S if (R := covering(Q, S, t)) is not None]
        if not cands:
            m.freeProb()
            return None  # tolerance: S looks weakly reachable
        pair = min(cands, key=lambda p: len(p[1]))
        pairs.append(pair)
        m.freeTransform()
        m.addCons(x[pair[0]] <= quicksum(x[r] for r in pair[1]))


# ---------------------------------------------------------------- upper bounds
def rational_witness(xi):
    v = [Fraction(max(float(z), 0.0)).limit_denominator(10**6) for z in xi]
    s = sum(v)
    return [z / s for z in v]


def snap(P, y, Qf, sets, wit):
    """Exact feasible rational Q near Qf (exact LP, relative L1 around Qf); its pi."""
    m = C.cone_masses(y, sets)
    if m is None:
        return None
    center = [[Fraction(float(v)).limit_denominator(10**9) for v in row] for row in Qf]
    _, Q = C.best_prices(center, y, sets, wit)
    if any(v <= 0 for row in Q for v in row):
        return None
    C.verify(P, y, Q, sets, m, wit)
    return pi_sym(P, Q), (Q, sets, m, wit)


def convex_step(P, sets, wit, time_limit):
    """min symmetric pi over Q > 0 with the fixed witnesses (SCIP, convex)."""
    T, d = P.shape
    m = _model(time_limit)
    a = {(t, i): m.addVar(lb=1e-3, ub=1e3) for t in range(T) for i in range(d)}
    g = {k: m.addVar(lb=0) for k in a}
    for k, v in a.items():
        m.addCons(g[k] >= v - 1)
        m.addCons(g[k] >= 1 / v - 1)
    for k, S in enumerate(sets):
        for t in S:
            xi = [float(z) for z in wit[k, t]]
            for s in range(T):
                if s not in S:
                    m.addCons(quicksum(xi[i] * (float(P[s, i]) * a[s, i] - float(P[t, i]) * a[t, i])
                                       for i in range(d) if xi[i]) >= 0)
    m.setObjective(quicksum(g.values()))
    m.optimize()
    if m.getNSols() == 0:
        m.freeProb()
        return None
    Q = np.array([[float(P[t, i]) * m.getVal(a[t, i]) for i in range(d)] for t in range(T)])
    m.freeProb()
    return Q


def max_margin(Q, S, t):
    T, d = Q.shape
    out = [s for s in range(T) if s not in S]
    if not out:
        return np.ones(d) / d
    c = np.zeros(d + 1)
    c[-1] = -1
    A = [np.concatenate([-(Q[s] - Q[t]), [1]]) for s in out]
    res = linprog(c, A_ub=A, b_ub=np.zeros(len(out)), A_eq=[[1.0] * d + [0.0]], b_eq=[1.0],
                  bounds=[(0, None)] * d + [(None, None)], method="highs")
    return res.x[:d]


def residual_family(Q, y, time_limit):
    """Weakly reachable spectra at Q carrying most of y, plus singletons for the rest."""
    T = len(y)
    cols = [frozenset(range(T))]
    while True:
        n = len(cols)
        A = np.array([[1.0 if t in S else 0.0 for S in cols] for t in range(T)]).reshape(T, n)
        res = linprog(np.concatenate([np.zeros(n), np.ones(T)]), A_eq=np.hstack([A, np.eye(T)]),
                      b_eq=y, bounds=[(0, None)] * (n + T), method="highs")
        dual = np.array(res.eqlin.marginals)
        value, S = _pricing(Q, dual, time_limit)
        if res.fun <= TOL or value <= TOL or S in cols:
            fam = [S for S, v in zip(cols, res.x[:n]) if v > 1e-12]
            return fam + [frozenset([t]) for t in range(T) if res.x[n + t] > 1e-12]
        cols.append(S)


def soft_pricing(Q, weights, eps, time_limit):
    """Like the pricing MILP, but each witness inequality may be violated by eps * scale."""
    T, d = Q.shape
    m = _model(time_limit)
    x = [m.addVar(vtype="B") for _ in range(T)]
    for t in range(T):
        xi = [m.addVar(lb=0, ub=1) for _ in range(d)]
        m.addCons(quicksum(xi) == 1)
        Mt = float(max(Q[t])) + 1.0
        for s in range(T):
            if s != t:
                gap = quicksum(xi[i] * float(Q[s, i] - Q[t, i]) for i in range(d))
                m.addCons(gap >= -Mt * (x[s] + 1 - x[t]) - eps * float(max(Q[t])))
    m.setObjective(quicksum(float(weights[t]) * x[t] for t in range(T)), "maximize")
    m.optimize()
    val, S = m.getObjVal(), frozenset(t for t in range(T) if m.getVal(x[t]) > 0.5)
    m.freeProb()
    return val, S


def soft_family(Q, y, eps, time_limit):
    """Column generation over eps-almost weakly reachable spectra; the family if it carries y."""
    T = len(y)
    cols = [frozenset(range(T))]
    while True:
        n = len(cols)
        A = np.array([[1.0 if t in S else 0.0 for S in cols] for t in range(T)]).reshape(T, n)
        res = linprog(np.concatenate([np.zeros(n), np.ones(T)]), A_eq=np.hstack([A, np.eye(T)]),
                      b_eq=y, bounds=[(0, None)] * (n + T), method="highs")
        if res.fun <= TOL * max(1.0, float(max(y))):
            return [S for S, v in zip(cols, res.x[:n]) if v > 1e-12]
        value, S = soft_pricing(Q, np.array(res.eqlin.marginals), eps, time_limit)
        if value <= TOL or S in cols:
            return None
        cols.append(S)


def repair(P, y, Q, time_limit, rounds=2):
    """Upper bound near Q: a family of (almost) weakly reachable spectra at Q, the witnesses
    fixed, the convex problem in Q makes them exact; then the exact rational snap."""
    best = None
    yf = np.array([float(v) for v in y])
    for eps in (1e-4, 1e-3, 1e-2, 1e-1):
        sets = soft_family(Q, yf, eps, time_limit)
        if sets is not None:
            cand = _repair_from(P, y, Q, sets, time_limit, rounds)
            if cand is not None and (best is None or cand[0] < best[0]):
                best = cand
            break
    cand = _repair_from(P, y, Q, residual_family(Q, yf, time_limit), time_limit, rounds)
    if cand is not None and (best is None or cand[0] < best[0]):
        best = cand
    return best


def _repair_from(P, y, Q, sets, time_limit, rounds):
    Pf = np.array([[float(v) for v in r] for r in P])
    best = None
    for _ in range(rounds):
        wit = {(k, t): rational_witness(max_margin(Q, S, t)) for k, S in enumerate(sets) for t in S}
        Qn = convex_step(Pf, sets, wit, time_limit)
        if Qn is None:
            break
        cand = snap(P, y, Qn, sets, wit)
        if cand is None or (best is not None and cand[0] >= best[0]):
            break
        best, Q = cand, Qn
    return best


def certify_point(P, y, Q, sets):
    """Exact certificate at a master point where the oracle said yes."""
    wit = {(k, t): rational_witness(max_margin(Q, S, t)) for k, S in enumerate(sets) for t in S}
    return snap(P, y, Q, sets, wit)


def constant_start(P, y):
    T, d = len(P), len(P[0])
    c = [min((P[t][i] for t in range(T)),
             key=lambda v: sum(max(v / P[s][i], P[s][i] / v) for s in range(T))) for i in range(d)]
    Q = [list(c) for _ in range(T)]
    levels = sorted(set(y))
    sets = [frozenset(t for t in range(T) if y[t] >= lv) for lv in levels]
    m = [lv - prev for lv, prev in zip(levels, [Fraction(0)] + levels[:-1])]
    wit = {(k, t): [Fraction(1, d)] * d for k, S in enumerate(sets) for t in S}
    C.verify(P, y, Q, sets, m, wit)
    return pi_sym(P, Q), (Q, sets, m, wit)


# ---------------------------------------------------------------- loop
def run(P, y, budget=1800.0, time_limit=300.0, tol=1e-6, depth=2, log=print):
    P = [[C.F(v) for v in row] for row in P]
    y = [C.F(v) for v in y]
    Pf = np.array([[float(v) for v in r] for r in P])
    yf = np.array([float(v) for v in y])
    T, d = Pf.shape
    grids = [SimplexGrid(d) for _ in range(T)]
    UB, cert = constant_start(P, y)
    cuts = [((t, (s,)),) for t in range(T) for s in range(T) if y[t] > y[s]]
    known = set()
    LB, t0, it, hist = 0.0, time.time(), 0, []
    while time.time() - t0 < budget:
        tl = max(10.0, min(time_limit, budget - (time.time() - t0)))
        ms = master(Pf, yf, cuts, grids, float(UB) * (1 + 1e-9) + 1e-12, tl)
        LB = max(LB, min(ms["bound"], float(UB)))
        note = [f"master {ms['status']}"]
        if ms["Q"] is None:
            hist.append((it, LB, float(UB), len(cuts), time.time() - t0))
            log(f"it {it:3d} LB {LB:.9f} UB {float(UB):.9f} no master solution [{note[0]}]")
            break
        Q = ms["Q"]
        loose = [(p, c) for p, c in ms["active"].items()
                 if cell_witness(grids[p[0]], c, Q, *p) < -TOL]
        ans, info = refute(Q, yf, tl)
        if ans == "yes":
            cand = certify_point(P, y, Q, info)
            if cand is not None and cand[0] < UB:
                UB, cert = cand
                note.append("POINT")
        else:
            w = integer_refutation(info, y)
            pairs = killing_pairs(Q, w, known, tl) if w is not None else None
            if pairs:
                cut = tuple(sorted(set(pairs)))
                if cut not in set(cuts):
                    cuts.append(cut)
                    known.update(cut)
                    note.append(f"cut {len(cut)}")
            else:
                note.append("no cut (tolerance)")
        if float(UB) - LB > tol:
            cand = repair(P, y, Q, tl)
            if cand is not None and cand[0] < UB:
                UB, cert = cand
                note.append("REPAIR")
        for (t, R), cell in sorted(loose, key=lambda x: -x[1]):
            ids = set(grids[t].cells[cell])
            for c2 in sorted([c2 for c2, cs in enumerate(grids[t].cells) if ids & set(cs)],
                             reverse=True):
                grids[t].subdivide(c2, depth)
        if loose:
            note.append(f"refined {len(loose)}")
        hist.append((it, LB, float(UB), len(cuts), time.time() - t0))
        log(f"it {it:3d} LB {LB:.9f} UB {float(UB):.9f} gap {float(UB) - LB:.2e} cuts {len(cuts)} "
            f"cells {sum(len(g.cells) for g in grids)} {time.time() - t0:7.1f}s [{' '.join(note)}]")
        if float(UB) - LB <= tol * max(1.0, float(UB)):
            break
        if ans == "no" and not loose and "cut" not in " ".join(note):
            break  # stalled (tolerance)
        it += 1
    return LB, UB, cert, hist


def main():
    from .datasets import berndt_wood, euklems

    names = sys.argv[1:]
    for name in names:
        P, y = berndt_wood(name[3:]) if name.startswith("BW:") else euklems(*name.split(":"))
        LB, UB, cert, hist = run(P, y, log=lambda s, n=name: print(n, s, flush=True))
        rec = dict(name=name, T=len(P), d=len(P[0]), LB=LB, UB=str(UB), UBf=float(UB),
                   gap=float(UB) - LB, history=hist,
                   Q=[[str(v) for v in r] for r in cert[0]], sets=[sorted(S) for S in cert[1]])
        print("RESULT", json.dumps({k: rec[k] for k in ("name", "LB", "UBf", "gap")}), flush=True)
        with open("cutloop_results.jsonl", "a") as f:
            f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    main()
