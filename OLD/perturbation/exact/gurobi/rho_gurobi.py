"""Minimal price perturbation rho_1 with MILP masters (Gurobi), standalone.

    rho_1(P, y) = min { sum_{t,i} |q_t^i / p_t^i - 1| : Q >= 0, y weakly solvable at Q }

y is weakly solvable at Q iff y = sum_k m_k 1_{S_k}, m_k >= 0, and every S_k is weakly
reachable: each t in S_k has a witness xi in the simplex with <xi, q_s - q_t> >= 0 for all
s outside S_k. K = T sets suffice, and the sets can be given distinct anchors k in S_k.

Lower master (valid lower bound): every t has a partition of the witness simplex into
cells; the witness of t in S_k lies in a cell and the inequality must hold at the vertex
of that cell where <., q_s - q_t> is maximal. With one cell per t this is the dominance
relaxation; refining the cells used by the master drives the bound to rho_1.
Upper master: witnesses are grid vertices (a restriction). Oracle: column generation at a
fixed Q with a pricing MILP. Upper bounds also come from a repair LP (witnesses fixed).

Usage:  python rho_gurobi.py instances.json [--out results.jsonl] [--names A B ...]
        [--iters 40] [--time 300] [--budget 900] [--threads 0] [--mem 8]
After each instance one JSON line (bounds, history, certificate) is appended to the
output file. Requires gurobipy and numpy.
"""

from __future__ import annotations

import argparse
import itertools
import json
import time
from fractions import Fraction as Fr

import gurobipy as gp
import numpy as np
from gurobipy import GRB

OPT = {"time": 300.0, "cap": 300.0, "threads": 0, "mem": 8.0}


# ---------------------------------------------------------------- witness grids
class Grid:
    """Partition of the standard simplex in R^d into simplicial cells (exact)."""

    def __init__(self, d):
        self.d = d
        self.vertices, self.index = [], {}
        unit = [tuple(Fr(int(i == j)) for j in range(d)) for i in range(d)]
        self.cells = [tuple(self.vertex(v) for v in unit)]

    def vertex(self, v):
        if v not in self.index:
            self.index[v] = len(self.vertices)
            self.vertices.append(v)
        return self.index[v]

    def dist2(self, a, b):
        return sum((x - y) ** 2 for x, y in zip(self.vertices[a], self.vertices[b]))

    def diam2(self, c):
        ids = self.cells[c]
        return max((self.dist2(a, b) for a, b in itertools.combinations(ids, 2)), default=0)

    def bisect(self, c):
        ids = self.cells[c]
        a, b = max(itertools.combinations(range(len(ids)), 2),
                   key=lambda e: self.dist2(ids[e[0]], ids[e[1]]))
        va, vb = self.vertices[ids[a]], self.vertices[ids[b]]
        mid = self.vertex(tuple((x + y) / 2 for x, y in zip(va, vb)))
        self.cells[c] = tuple(mid if i == a else v for i, v in enumerate(ids))
        self.cells.append(tuple(mid if i == b else v for i, v in enumerate(ids)))

    def subdivide(self, c, depth):
        group = [c]
        for _ in range(depth):
            nxt = []
            for g in group:
                self.bisect(g)
                nxt += [g, len(self.cells) - 1]
            group = nxt

    def refine_coarsest(self):
        top = max(self.diam2(c) for c in range(len(self.cells)))
        for c in [c for c in range(len(self.cells)) if self.diam2(c) == top]:
            self.bisect(c)

    def contains(self, c, xi, tol=1e-12):
        V = np.array([[float(x) for x in self.vertices[j]] for j in self.cells[c]]).T
        lam = np.linalg.lstsq(V, np.array(xi, float), rcond=None)[0]
        return bool(np.all(lam >= -tol)) and np.allclose(V @ lam, xi, atol=1e-9)


# ---------------------------------------------------------------- models
def new_model(time_limit=None):
    m = gp.Model()
    m.Params.OutputFlag = 0
    m.Params.TimeLimit = time_limit or OPT["time"]
    m.Params.MIPGap = 0.0
    m.Params.MIPGapAbs = 0.0
    m.Params.FeasibilityTol = 1e-9
    m.Params.IntFeasTol = 1e-9
    m.Params.Threads = OPT["threads"]
    m.Params.SoftMemLimit = OPT["mem"]
    return m


def family(m, y):
    """z[k,t] (t in S_k), m_k; w = m z; sum_k w = y; anchors z[k,k] = 1."""
    T = len(y)
    ymax = float(max(y))
    z = m.addVars(T, T, vtype=GRB.BINARY, name="z")
    mk = m.addVars(T, lb=0, name="m")
    w = m.addVars(T, T, lb=0, name="w")
    for k in range(T):
        z[k, k].LB = 1
        mk[k].UB = float(y[k])
        for t in range(T):
            w[k, t].UB = float(y[t])
            m.addConstr(w[k, t] <= mk[k])
            m.addConstr(w[k, t] <= float(y[t]) * z[k, t])
            m.addConstr(w[k, t] >= mk[k] - ymax * (1 - z[k, t]))
    for t in range(T):
        m.addConstr(gp.quicksum(w[k, t] for k in range(T)) == float(y[t]))
    return z, mk


def master(P, y, grids, ub, kind, tracked, start=None):
    """kind: 'dominance' (no family), 'lower' or 'upper'. Returns a dict or None."""
    T, d = P.shape
    m = new_model()
    q = m.addVars(T, d, lb=0, name="q")
    e = m.addVars(T, d, lb=0, name="e")
    for t in range(T):
        for i in range(d):
            q[t, i].UB = float(P[t, i]) * (1 + ub)
            m.addConstr(e[t, i] >= q[t, i] / float(P[t, i]) - 1)
            m.addConstr(e[t, i] >= 1 - q[t, i] / float(P[t, i]))
    obj = e.sum()
    m.addConstr(obj <= ub)
    m.setObjective(obj, GRB.MINIMIZE)
    Mt = [float(max(P[t])) * (1 + ub) for t in range(T)]
    # valid: y_t > y_s => q_t^i <= q_s^i for some i
    for t, s in itertools.permutations(range(T), 2):
        if y[t] > y[s]:
            dl = m.addVars(d, vtype=GRB.BINARY)
            m.addConstr(dl.sum() >= 1)
            for i in range(d):
                m.addConstr(q[t, i] - q[s, i] <= Mt[t] * (1 - dl[i]))
                dl[i].BranchPriority = 10
    if kind == "dominance":
        m.optimize()
        if m.SolCount == 0:
            return None
        return dict(Q=np.array([[q[t, i].X for i in range(d)] for t in range(T)]),
                    value=m.ObjVal, bound=m.ObjBound, z=None)
    z, mk = family(m, y)

    def lhs(v, s, t):
        return gp.quicksum(float(v[i]) * (q[s, i] - q[t, i]) for i in range(d) if v[i])

    sel, sign, nv = {}, {}, {}

    def beats(t, s, a, b):
        """1 iff <v_a - v_b, q_s - q_t> >= 0 (ties either way); shared over k, cells."""
        u = [float(x - y_) for x, y_ in zip(grids[t].vertices[a], grids[t].vertices[b])]
        top = max(abs(x) for x in u)
        u = [x / top for x in u]
        flip = next(x for x in u if x != 0) < 0
        key = (t, s, tuple(round(-x if flip else x, 12) for x in u))
        if key not in sign:
            x = sign[key] = m.addVar(vtype=GRB.BINARY)
            uu = key[2]
            dd = gp.quicksum(uu[i] * (q[s, i] - q[t, i]) for i in range(d))
            big = sum(abs(uu[i]) * float(max(P[s, i], P[t, i])) for i in range(d)) * (1 + ub)
            m.addConstr(dd >= -big * (1 - x))
            m.addConstr(dd <= big * x)
        return 1 - sign[key] if flip else sign[key]

    def need(t, s, j):
        """1 forces <v_j, q_s - q_t> >= 0."""
        if (t, s, j) not in nv:
            v = grids[t].vertices[j]
            x = nv[t, s, j] = m.addVar(lb=0, ub=1)
            big = sum(float(v[i]) * float(P[t, i]) for i in range(d)) * (1 + ub)
            m.addConstr(lhs(v, s, t) >= -big * (1 - x))
        return nv[t, s, j]

    for k in range(T):
        for t in range(T):
            g = grids[t]
            if kind == "upper":
                verts = sorted({j for ids in g.cells for j in ids})
                a = sel[k, t] = {j: m.addVar(vtype=GRB.BINARY) for j in verts}
                m.addConstr(gp.quicksum(a.values()) == 1)
                for s in range(T):
                    if s != t:
                        for j in verts:
                            slack = (1 - a[j]) + z[k, s] + (1 - z[k, t])
                            m.addConstr(lhs(g.vertices[j], s, t) >= -Mt[t] * slack)
            elif t in tracked:
                c = sel[k, t] = {ci: m.addVar(vtype=GRB.BINARY) for ci in range(len(g.cells))}
                m.addConstr(gp.quicksum(c.values()) == z[k, t])
                for s in range(T):
                    if s == t:
                        continue
                    for ci, ids in enumerate(g.cells):
                        for j in ids:
                            lose = gp.quicksum(1 - beats(t, s, j, l) for l in ids if l != j)
                            m.addConstr(need(t, s, j) >= c[ci] - z[k, s] - lose)
                        if k == 0:  # no cyclic signs on ties (d >= 3)
                            for a_, b_, e_ in itertools.combinations(ids, 3):
                                cyc = beats(t, s, a_, b_) + beats(t, s, b_, e_) + beats(t, s, e_, a_)
                                m.addConstr(cyc >= 1)
                                m.addConstr(cyc <= 2)
    if start is not None:  # MIP start from the best certificate
        for t in range(T):
            for i in range(d):
                q[t, i].Start = float(start["Q"][t][i])
        for (k, t), v in z.items():
            v.Start = start["z"][k][t]
        for k in range(T):
            mk[k].Start = start["m"][k]
    m.optimize()
    if m.SolCount == 0:
        return dict(Q=None, value=float("inf"), bound=m.ObjBound if m.Status != GRB.INFEASIBLE else ub)
    out = dict(Q=np.array([[q[t, i].X for i in range(d)] for t in range(T)]),
               value=m.ObjVal, bound=m.ObjBound if m.Status != GRB.INFEASIBLE else ub,
               z=np.array([[round(z[k, t].X) for t in range(T)] for k in range(T)]),
               m=np.array([mk[k].X for k in range(T)]),
               sel={key: max(vs, key=lambda j: vs[j].X) for key, vs in sel.items()})
    m.dispose()
    return out


def witness_lp(Q, S, t, V=None):
    """max over xi in conv(V) (default: the simplex) of min_{s not in S} <xi, q_s - q_t>."""
    T, d = Q.shape
    V = np.eye(d) if V is None else np.array(V, float)
    out = [s for s in range(T) if s not in S]
    if not out:
        return 1.0, V.mean(axis=0)
    m = new_model(60)
    lam = m.addVars(len(V), lb=0)
    tau = m.addVar(lb=-GRB.INFINITY)
    m.addConstr(lam.sum() == 1)
    for s in out:
        diff = Q[s] - Q[t]
        m.addConstr(gp.quicksum(lam[j] * float(V[j] @ diff) for j in range(len(V))) >= tau)
    m.setObjective(tau, GRB.MAXIMIZE)
    m.optimize()
    xi = sum(lam[j].X * V[j] for j in range(len(V)))
    val = tau.X
    m.dispose()
    return val, xi


def oracle(Q, y):
    """Column generation: is y in cone{1_S : S weakly reachable at Q}? -> (ok, sets)."""
    T, d = Q.shape
    cols = [frozenset(range(T))]
    pr = new_model()
    x = pr.addVars(T, vtype=GRB.BINARY)
    for t in range(T):
        xi = pr.addVars(d, lb=0)
        pr.addConstr(xi.sum() == 1)
        Mt = float(max(Q[t])) + 1
        for s in range(T):
            if s != t:
                gap = gp.quicksum(xi[i] * float(Q[s, i] - Q[t, i]) for i in range(d))
                pr.addConstr(gap >= -Mt * (x[s] + 1 - x[t]))
    while True:
        lp = new_model()
        mv = lp.addVars(len(cols), lb=0)
        a = lp.addVars(T, lb=0)
        rows = [lp.addConstr(gp.quicksum(mv[c] for c, S in enumerate(cols) if t in S) + a[t]
                             == float(y[t])) for t in range(T)]
        lp.setObjective(a.sum(), GRB.MINIMIZE)
        lp.optimize()
        if lp.ObjVal <= 1e-9 * max(1.0, float(max(y))):
            return True, [S for c, S in enumerate(cols) if mv[c].X > 1e-12]
        dual = [r.Pi for r in rows]
        lp.dispose()
        pr.setObjective(gp.quicksum(dual[t] * x[t] for t in range(T)), GRB.MAXIMIZE)
        pr.optimize()
        S = frozenset(t for t in range(T) if x[t].X > 0.5)
        if pr.ObjVal <= 1e-9 or S in cols:
            return False, None
        cols.append(S)


def cone_masses(y, sets):
    T = len(y)
    m = new_model(60)
    mv = m.addVars(len(sets), lb=0)
    for t in range(T):
        m.addConstr(gp.quicksum(mv[k] for k, S in enumerate(sets) if t in S) == float(y[t]))
    m.optimize()
    if m.Status != GRB.OPTIMAL:
        return None
    return [mv[k].X for k in range(len(sets))]


def best_prices(P, sets, wit):
    """LP: min pi_1 over Q >= 0 with fixed sets and witnesses (always feasible)."""
    T, d = P.shape
    m = new_model(120)
    q = m.addVars(T, d, lb=0)
    e = m.addVars(T, d, lb=0)
    for t in range(T):
        for i in range(d):
            m.addConstr(e[t, i] >= q[t, i] / float(P[t, i]) - 1)
            m.addConstr(e[t, i] >= 1 - q[t, i] / float(P[t, i]))
    for k, S in enumerate(sets):
        for t in S:
            xi = wit[k, t]
            for s in range(T):
                if s not in S:
                    m.addConstr(gp.quicksum(float(xi[i]) * (q[s, i] - q[t, i]) for i in range(d)) >= 0)
    m.setObjective(e.sum(), GRB.MINIMIZE)
    m.optimize()
    Q = np.array([[q[t, i].X for i in range(d)] for t in range(T)])
    m.dispose()
    return float(np.abs(Q / P - 1).sum()), Q


def certificate(P, y, Q, sets, wit, tag):
    ms = cone_masses(y, sets)
    if ms is None:
        return None
    return dict(value=float(np.abs(Q / P - 1).sum()), source=tag,
                Q=Q.tolist(), sets=[sorted(S) for S in sets], m=ms,
                witness={f"{k},{t}": [str(Fr(v).limit_denominator(10**12)) if not isinstance(v, Fr)
                                      else str(v) for v in xi]
                         for (k, t), xi in wit.items()})


def repair(P, y, Q, sets, rounds=3):
    best = None
    for _ in range(rounds):
        wit = {(k, t): witness_lp(Q, S, t)[1] for k, S in enumerate(sets) for t in S}
        val, Qn = best_prices(P, sets, wit)
        if best is not None and val >= best["value"] - 1e-12:
            break
        best, Q = certificate(P, y, Qn, sets, wit, "repair"), Qn
        if best is None:
            return None
    return best


def as_start(cert, T):
    """Anchor the certificate's sets (bipartite matching) for a MIP start."""
    if cert is None:
        return None
    sets = [frozenset(S) for S, mm in zip(cert["sets"], cert["m"]) if mm > 1e-12]
    ms = [mm for mm in cert["m"] if mm > 1e-12]
    owner = {}

    def aug(k, seen):
        for t in sorted(sets[k]):
            if t not in seen:
                seen.add(t)
                if t not in owner or aug(owner[t], seen):
                    owner[t] = k
                    return True
        return False

    if not all(aug(k, set()) for k in range(len(sets))):
        return None
    Z = [[1] * T for _ in range(T)]
    M = [0.0] * T
    for t, k in owner.items():
        Z[t] = [int(s in sets[k]) for s in range(T)]
        M[t] = ms[k]
    return dict(Q=cert["Q"], z=Z, m=M)


# ---------------------------------------------------------------- main loop
def run(name, P, y, iters, tol, depth=2, upper_every=4, results=None, budget=None):
    P, y = np.array(P, float), np.array(y, float)
    T, d = P.shape
    grids = [Grid(d) for _ in range(T)]
    tracked = set(range(T))
    # start: all prices equal (every set weakly reachable), level sets of y
    c = [min(P[:, i], key=lambda v: np.abs(v / P[:, i] - 1).sum()) for i in range(d)]
    levels = sorted(set(y))
    sets0 = [frozenset(np.flatnonzero(y >= lv).tolist()) for lv in levels]
    Q0 = np.tile(c, (T, 1))
    best = certificate(P, y, Q0, sets0, {(k, t): [Fr(1, d)] * d for k, S in enumerate(sets0)
                                          for t in S}, "constant")
    LB, hist, t0 = 0.0, [], time.time()
    rec = dict(name=name, T=T, d=d, P=P.tolist(), y=y.tolist())
    for it in range(iters):
        if budget is not None:  # no MILP may run past the budget of the instance
            OPT["time"] = max(10.0, min(OPT["cap"], budget - (time.time() - t0)))
        UB = best["value"]
        kind = "dominance" if it == 0 else "lower"
        tl = time.time()
        lo = master(P, y, grids, UB + 1e-9, kind, tracked,
                    start=as_start(best, T) if kind == "lower" else None)
        LB = max(LB, min(lo["bound"], UB))
        note = [f"lo {time.time() - tl:.1f}s"]
        split = {}
        if lo["Q"] is not None:
            Qlo = lo["Q"]
            sets, cells = [], {}
            if lo["z"] is not None:
                for k in range(T):
                    S = frozenset(np.flatnonzero(lo["z"][k]).tolist())
                    if lo["m"][k] > 1e-12 and S:
                        cells.update({(len(sets), t): lo["sel"][k, t] for t in S})
                        sets.append(S)
                for k, S in enumerate(sets):
                    for t in S:
                        V = [grids[t].vertices[j] for j in grids[t].cells[cells[k, t]]]
                        tau, xi = witness_lp(Qlo, S, t, V)
                        if tau < -1e-9:
                            split.setdefault((t, cells[k, t]), xi)
                if not split:
                    wit = {(k, t): witness_lp(Qlo, S, t)[1] for k, S in enumerate(sets) for t in S}
                    cert = certificate(P, y, Qlo, sets, wit, "family")
                    if cert and cert["value"] < best["value"]:
                        best = cert
                        note.append("FAMILY")
            if best["value"] - LB > tol:
                tl = time.time()
                ok, cand = oracle(Qlo, y)
                note.append(f"oracle {time.time() - tl:.1f}s")
                if ok:
                    wit, good = {}, []
                    for S in cand:
                        ws = {t: witness_lp(Qlo, S, t) for t in S}
                        if all(v[0] >= -1e-9 for v in ws.values()):
                            wit.update({(len(good), t): v[1] for t, v in ws.items()})
                            good.append(S)
                    cert = certificate(P, y, Qlo, good, wit, "oracle")
                    if cert and cert["value"] < best["value"]:
                        best = cert
                        note.append("ORACLE")
            if best["value"] - LB > tol:
                cert = repair(P, y, Qlo, sets or sets0)
                if cert and cert["value"] < best["value"]:
                    best = cert
                    note.append("REPAIR")
        if best["value"] - LB > tol and it > 0 and it % upper_every == 0:
            tl = time.time()
            up = master(P, y, grids, best["value"] + 1e-9, "upper", tracked, start=as_start(best, T))
            note.append(f"upper {time.time() - tl:.1f}s")
            if up["Q"] is not None:
                usets = [frozenset(np.flatnonzero(r).tolist()) for r in up["z"]]
                wit = {(k, t): grids[t].vertices[up["sel"][k, t]] for k, S in enumerate(usets) for t in S}
                val, Qx = best_prices(P, usets, wit)
                cert = certificate(P, y, Qx, usets, wit, "upper")
                if cert and cert["value"] < best["value"]:
                    best = cert
                    note.append("UPPER")
        UB = best["value"]
        ncells = sum(len(g.cells) for g in grids)
        hist.append(dict(it=it, LB=LB, UB=UB, cells=ncells, seconds=time.time() - t0, note=" ".join(note)))
        print(f"{name} it {it:2d} LB {LB:.9f} UB {UB:.9f} gap {UB - LB:.2e} cells {ncells:4d} "
              f"{time.time() - t0:7.1f}s [{' '.join(note)}]", flush=True)
        rec.update(LB=LB, UB=UB, history=hist, best=best,
                   status="closed" if UB - LB <= tol else "running")
        if results is not None:
            results[name] = rec
        if UB - LB <= tol:
            break
        if budget is not None and time.time() - t0 > budget:
            break
        todo = set()
        for t, cell in split:
            ids = set(grids[t].cells[cell])
            todo |= {(t, c_) for c_, cs in enumerate(grids[t].cells) if ids & set(cs)}
        for t, cell in sorted(todo, key=lambda x: (x[0], -x[1])):
            grids[t].subdivide(cell, depth)
        if (not todo and kind == "lower") or (it >= 7 and (it + 2) & (it + 1) == 0):
            for g in grids:
                g.refine_coarsest()
    rec["status"] = "closed" if rec["UB"] - rec["LB"] <= tol else "stopped (iterations or budget)"
    return rec


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("instances")
    ap.add_argument("--out", default="results.jsonl", help="one JSON line per instance")
    ap.add_argument("--names", nargs="*")
    ap.add_argument("--iters", type=int, default=40)
    ap.add_argument("--time", type=float, default=300.0, help="seconds per MILP")
    ap.add_argument("--threads", type=int, default=0, help="0 = all cores")
    ap.add_argument("--mem", type=float, default=8.0, help="GB per model (SoftMemLimit)")
    ap.add_argument("--tol", type=float, default=1e-6)
    ap.add_argument("--budget", type=float, default=900.0, help="seconds per instance")
    a = ap.parse_args()
    OPT.update(time=a.time, cap=a.time, threads=a.threads, mem=a.mem)
    inst = json.load(open(a.instances))
    version = ".".join(map(str, gp.gurobi.version()))
    for name in a.names or list(inst):
        P = [[float(Fr(v)) for v in row] for row in inst[name]["P"]]
        y = [float(Fr(v)) for v in inst[name]["y"]]
        partial = {}
        try:
            rec = run(name, P, y, a.iters, a.tol, results=partial, budget=a.budget)
        except Exception as exc:  # record what there is and go on with the next instance
            rec = dict(partial.get(name, dict(name=name)), status="error", error=repr(exc))
            print(name, "ERROR", repr(exc), flush=True)
        rec.update(gurobi=version, settings=vars(a), finished=time.strftime("%Y-%m-%d %H:%M:%S"))
        with open(a.out, "a") as f:  # one line per finished instance
            f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    main()
