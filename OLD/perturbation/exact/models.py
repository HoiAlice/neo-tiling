"""MILP models: the oracle and the two masters.

Data: prices P (T x d, positive), outputs y (T, positive). Cost of a price set Q >= 0
(this is the linear modification of the notes' perturbation):

    pi_1(P, Q) = sum_{t, i} |q^i_t / p^i_t - 1|.

By the criterion of weak solvability (notes, thm:closure) y is weakly solvable at Q iff
y = sum_k m_k 1_{S_k} with m_k >= 0 and every S_k weakly reachable at Q, and by
Caratheodory K = T sets suffice. Common variables of all models:

    z[k, t] in {0, 1}   t in S_k,
    m[k] >= 0, w[k, t] = m[k] z[k, t],   sum_k w[k, t] = y_t.

Weak reachability of S_k needs, for t in S_k and s outside S_k, a common witness xi of t
with <xi, q_s - q_t> >= 0. The models differ only in how xi is treated:

* `oracle`: Q fixed, xi continuous in the simplex. Exact decision of weak solvability;
* `lower`:  Q variable, xi in a cell of a partition, the inequality at some vertex of
            that cell, the vertex chosen per s. A relaxation, so its optimum is a lower
            bound for rho_1. With the trivial partition (one cell, vertices e_i) it is
            the dominance relaxation;
* `upper`:  Q variable, xi a vertex of the partition. A restriction: every feasible
            point is weakly solvable with explicit witnesses, so it gives upper bounds.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field

import numpy as np
from pyscipopt import Model, quicksum

from .grid import SimplexGrid


@dataclass
class Solution:
    status: str
    value: float
    bound: float
    Q: np.ndarray | None = None
    z: np.ndarray | None = None
    m: np.ndarray | None = None
    cells: dict = field(default_factory=dict)  # (k, t) -> cell index (lower)
    witness: dict = field(default_factory=dict)  # (k, t) -> vertex index or xi


MEMORY_MB = 2000  # per SCIP model; status "memlimit" keeps a valid dual bound
DOMINANCE = {"use": True, "priority": 10}  # dominance disjunctions in the masters


def _common(model: Model, y: np.ndarray, K: int):
    T = len(y)
    ymax = float(max(y))
    z = {(k, t): model.addVar(vtype="B", name=f"z{k}_{t}") for k in range(K) for t in range(T)}
    m = {k: model.addVar(lb=0, ub=ymax, name=f"m{k}") for k in range(K)}
    w = {
        (k, t): model.addVar(lb=0, ub=float(y[t]), name=f"w{k}_{t}")
        for k in range(K)
        for t in range(T)
    }
    for k in range(K):
        for t in range(T):
            model.addCons(w[k, t] <= m[k])
            model.addCons(w[k, t] <= float(y[t]) * z[k, t])
            model.addCons(w[k, t] >= m[k] - ymax * (1 - z[k, t]))
        if K == T:
            # anchors: take linearly independent indicators (Caratheodory); a nonsingular
            # 0/1 matrix has a transversal of ones, so the sets get distinct anchors
            # k in S_k; an unused slot is the full set. Removes the slot symmetry.
            model.chgVarLb(z[k, k], 1)
            model.chgVarUb(m[k], float(y[k]))
        elif k + 1 < K:
            model.addCons(m[k] >= m[k + 1])
    for t in range(T):
        model.addCons(quicksum(w[k, t] for k in range(K)) == float(y[t]))
    return z, m, w


def _prices(model: Model, P: np.ndarray, ub: float):
    T, d = P.shape
    q = {
        (t, i): model.addVar(lb=0, ub=float(P[t, i]) * (1 + ub), name=f"q{t}_{i}")
        for t in range(T)
        for i in range(d)
    }
    e = {(t, i): model.addVar(lb=0, name=f"e{t}_{i}") for t in range(T) for i in range(d)}
    for t in range(T):
        for i in range(d):
            model.addCons(e[t, i] >= q[t, i] / float(P[t, i]) - 1)
            model.addCons(e[t, i] >= 1 - q[t, i] / float(P[t, i]))
    obj = quicksum(e.values())
    model.addCons(obj <= ub)
    model.setObjective(obj, "minimize")
    return q, obj


def _new(time_limit: float, threads: int = 1) -> Model:
    model = Model()
    model.hideOutput()
    model.setParam("limits/time", time_limit)
    model.setParam("limits/gap", 0.0)
    model.setParam("limits/absgap", 0.0)
    model.setParam("numerics/feastol", 1e-9)
    # SCIP has no memory limit by default; a hard MILP grows its tree without bound
    model.setParam("limits/memory", MEMORY_MB)
    return model


def _extract(model, q, z, m, T, d, K) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    Q = np.array([[model.getVal(q[t, i]) for i in range(d)] for t in range(T)])
    if not z:
        return Q, None, None
    Z = np.array([[round(model.getVal(z[k, t])) for t in range(T)] for k in range(K)])
    M = np.array([model.getVal(m[k]) for k in range(K)])
    return Q, Z, M


def build_master(
    P: np.ndarray,
    y: np.ndarray,
    grids: list[SimplexGrid],
    ub: float,
    kind: str,
    time_limit: float = 600.0,
    K: int | None = None,
    start: Solution | None = None,
    tracked: set[int] | None = None,
):
    """The lower ('lower') or upper ('upper') master for the partitions `grids[t]`;
    'dominance' is the lower master of the trivial partition in compact form.

    In the lower master the witness constraints are imposed only for t in `tracked`
    (all t if None): dropping constraints keeps it a relaxation."""
    T, d = P.shape
    K = K or T
    model = _new(time_limit)
    q, obj = _prices(model, P, ub)
    if kind == "dominance":
        # the lower master of the trivial partition, without the family: its spectra
        # are the down-sets of strict dominance, so it reduces to these disjunctions
        z, m = {}, {}
    else:
        z, m, _ = _common(model, y, K)
    Mt = [float(max(P[t])) * (1 + ub) for t in range(T)]

    def lhs(v, s, t):
        return quicksum(float(v[i]) * (q[s, i] - q[t, i]) for i in range(d))

    # Valid for every weakly solvable Q (some spectrum contains t and misses s):
    # y_t > y_s => q_t^i <= q_s^i for some i. Implied by the rest; branched on first.
    for t in range(T if DOMINANCE["use"] or kind == "dominance" else 0):
        for s in range(T):
            if y[t] > y[s]:
                dl = [model.addVar(vtype="B", name=f"dom{t}_{s}_{i}") for i in range(d)]
                model.addCons(quicksum(dl) >= 1)
                for i in range(d):
                    model.addCons(q[t, i] - q[s, i] <= Mt[t] * (1 - dl[i]))
                    model.chgVarBranchPriority(dl[i], DOMINANCE["priority"])

    sel, sign, nv = {}, {}, {}

    # f(xi) = <xi, q_s - q_t> is linear, so on a cell it is >= 0 somewhere iff it is >= 0
    # at the maximizing vertex; vertex j maximizes iff <v_j - v_l, q_s - q_t> >= 0 for the
    # other vertices l of the cell. Bisection produces finitely many edge directions u; the
    # signs of <u, q_s - q_t> and the vertex claims depend on Q only, so they are shared by
    # all k and all cells.
    def beats(t, s, a, b):
        """A 0/1 expression equal to 1 iff <v_a - v_b, q_s - q_t> >= 0 (up to ties)."""
        va, vb = grids[t].vertices[a], grids[t].vertices[b]
        u = [float(x - y) for x, y in zip(va, vb)]
        top = max(abs(x) for x in u)
        u = [x / top for x in u]
        flip = next(x for x in u if x != 0) < 0
        key = (t, s, tuple(round(-x if flip else x, 12) for x in u))
        if key not in sign:
            sign[key] = x = model.addVar(vtype="B", name=f"sg{len(sign)}")
            uu = key[2]
            dd = quicksum(uu[i] * (q[s, i] - q[t, i]) for i in range(d))
            big = sum(abs(uu[i]) * float(max(P[s, i], P[t, i])) for i in range(d)) * (1 + ub)
            model.addCons(dd >= -big * (1 - x))
            model.addCons(dd <= big * x)
        return 1 - sign[key] if flip else sign[key]

    def need(t, s, j):
        """nv = 1 forces <v_j, q_s - q_t> >= 0."""
        if (t, s, j) not in nv:
            v = grids[t].vertices[j]
            nv[t, s, j] = x = model.addVar(lb=0, ub=1, name=f"n{t}_{s}_{j}")
            big = sum(float(v[i]) * float(P[t, i]) * (1 + ub) for i in range(d))
            model.addCons(lhs(v, s, t) >= -big * (1 - x))
        return nv[t, s, j]

    for k in range(K if kind != "dominance" else 0):
        for t in range(T):
            g = grids[t]
            verts = g.used_vertices()
            if kind == "upper":
                a = {j: model.addVar(vtype="B", name=f"a{k}_{t}_{j}") for j in verts}
                model.addCons(quicksum(a.values()) == 1)
                sel[k, t] = a
                for s in range(T):
                    if s == t:
                        continue
                    for j in verts:
                        slack = (1 - a[j]) + z[k, s] + (1 - z[k, t])
                        model.addCons(lhs(g.vertices[j], s, t) >= -Mt[t] * slack)
            elif tracked is None or t in tracked:
                c = {
                    ci: model.addVar(vtype="B", name=f"c{k}_{t}_{ci}")
                    for ci in range(len(g.cells))
                }
                model.addCons(quicksum(c.values()) == z[k, t])  # a cell iff t in S_k
                sel[k, t] = c
                for s in range(T):
                    if s == t:
                        continue
                    for ci, ids in enumerate(g.cells):
                        for j in ids:
                            lose = quicksum(1 - beats(t, s, j, l) for l in ids if l != j)
                            model.addCons(need(t, s, j) >= c[ci] - z[k, s] - lose)
                        if k == 0:
                            # ties may leave the signs cyclic; forbid cycles on every
                            # triple, so the cell always has a vertex beating the others
                            for a, b2, e in itertools.combinations(ids, 3):
                                cyc = beats(t, s, a, b2) + beats(t, s, b2, e) + beats(t, s, e, a)
                                model.addCons(cyc >= 1)
                                model.addCons(cyc <= 2)

    if start is not None and kind == "lower" and start.Q is not None:
        sol = model.createPartialSol()
        for (t, i), var in q.items():
            model.setSolVal(sol, var, float(start.Q[t, i]))
        for (k, t), var in z.items():
            model.setSolVal(sol, var, float(start.z[k, t]))
        for k, var in m.items():
            model.setSolVal(sol, var, float(start.m[k]))
        for (k, t), cvars in sel.items():
            if start.z[k, t] and (k, t) in start.cells:
                for ci, var in cvars.items():
                    model.setSolVal(sol, var, float(ci == start.cells[k, t]))
        model.addSol(sol)
    if start is not None and kind == "upper" and start.Q is not None:
        sol = model.createSol()
        for (t, i), var in q.items():
            model.setSolVal(sol, var, float(start.Q[t, i]))
        for (k, t), var in z.items():
            model.setSolVal(sol, var, float(start.z[k, t]))
        for k, var in m.items():
            model.setSolVal(sol, var, float(start.m[k]))
        for (k, t), a in sel.items():
            for j, var in a.items():
                model.setSolVal(sol, var, float(start.witness.get((k, t)) == j))
        model.addSol(sol, free=True)
    return model, q, z, m, sel


def solve_master(
    P, y, grids, ub, kind, time_limit=600.0, K=None, start=None, tracked=None
) -> Solution:
    T, d = P.shape
    K = K or T
    model, q, z, m, sel = build_master(P, y, grids, ub, kind, time_limit, K, start, tracked)
    model.optimize()
    status = model.getStatus()
    bound = model.getDualbound() if status != "infeasible" else ub
    if model.getNSols() == 0:
        model.freeProb()
        return Solution(status, float("inf"), bound)
    Q, Z, M = _extract(model, q, z, m, T, d, K)
    chosen = {
        key: max(vs, key=lambda j: model.getVal(vs[j])) for key, vs in sel.items()
    }
    out = Solution(status, model.getObjVal(), bound, Q, Z, M)
    model.freeProb()
    if kind == "upper":
        out.witness = chosen
    else:
        out.cells = chosen
    return out


def _pricing(Q: np.ndarray, weights: np.ndarray, time_limit: float):
    """max sum_t weights_t over spectra S weakly reachable at the fixed Q (MILP)."""
    T, d = Q.shape
    model = _new(time_limit)
    x = [model.addVar(vtype="B", name=f"x{t}") for t in range(T)]
    Mt = [float(max(Q[t])) + 1.0 for t in range(T)]
    for t in range(T):
        xi = [model.addVar(lb=0, ub=1, name=f"xi{t}_{i}") for i in range(d)]
        model.addCons(quicksum(xi) == 1)
        for s in range(T):
            if s != t:
                gap = quicksum(xi[i] * float(Q[s, i] - Q[t, i]) for i in range(d))
                model.addCons(gap >= -Mt[t] * (x[s] + 1 - x[t]))
    model.setObjective(quicksum(float(weights[t]) * x[t] for t in range(T)), "maximize")
    model.optimize()
    if model.getStatus() != "optimal":
        raise RuntimeError(f"pricing: {model.getStatus()}")
    return model.getObjVal(), frozenset(t for t in range(T) if model.getVal(x[t]) > 0.5)


def oracle(Q: np.ndarray, y: np.ndarray, time_limit: float = 600.0, eps: float = 1e-9):
    """Column generation for y in cone{1_S : S weakly reachable at the fixed Q >= 0}.

    Phase 1 LP min sum a s.t. sum_S m_S 1_S + a = y; pricing over weakly reachable S.
    Returns (feasible, sets): the spectra carrying y when feasible. The sets are
    checked exactly afterwards; infeasibility is decided by the LP duals.
    """
    from scipy.optimize import linprog

    T = len(y)
    cols = [frozenset(range(T))]
    while True:
        n = len(cols)
        A = np.array([[1.0 if t in S else 0.0 for S in cols] for t in range(T)]).reshape(T, n)
        res = linprog(
            np.concatenate([np.zeros(n), np.ones(T)]),
            A_eq=np.hstack([A, np.eye(T)]),
            b_eq=y,
            bounds=[(0, None)] * (n + T),
            method="highs",
        )
        if res.fun <= eps * max(1.0, float(max(y))):
            return True, [S for S, v in zip(cols, res.x[:n]) if v > 1e-12]
        dual = np.array(res.eqlin.marginals)
        value, S = _pricing(Q, dual, time_limit)
        if value <= eps or S in cols:
            return False, None
        cols.append(S)


def oracle_milp(Q: np.ndarray, y: np.ndarray, time_limit: float = 600.0, K: int | None = None):
    """MILP decision: is y weakly solvable at the fixed prices Q >= 0?

    Returns (feasible, z, m, xi) with xi[k, t] a weak witness of t for S_k.
    """
    T, d = Q.shape
    K = K or T
    model = _new(time_limit)
    model.setObjective(0)
    z, m, _ = _common(model, y, K)
    Mt = [float(max(Q[t])) + 1.0 for t in range(T)]
    xi = {
        (k, t): [model.addVar(lb=0, ub=1, name=f"x{k}_{t}_{i}") for i in range(d)]
        for k in range(K)
        for t in range(T)
    }
    for (k, t), x in xi.items():
        model.addCons(quicksum(x) == 1)
        for s in range(T):
            if s != t:
                gap = quicksum(x[i] * float(Q[s, i] - Q[t, i]) for i in range(d))
                model.addCons(gap >= -Mt[t] * (z[k, s] + 1 - z[k, t]))
    model.optimize()
    if model.getNSols() == 0:
        return False, None, None, None
    Z = np.array([[round(model.getVal(z[k, t])) for t in range(T)] for k in range(K)])
    M = np.array([model.getVal(m[k]) for k in range(K)])
    X = {key: np.array([model.getVal(v) for v in x]) for key, x in xi.items()}
    return True, Z, M, X
