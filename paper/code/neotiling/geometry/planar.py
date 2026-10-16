"""(Weak) solvability at fixed prices in the plane: the chain graph and its flow LP.

Mirrors `lean/PolyHardness/FlowLP.lean`.  Prices are T points p_t = (X_t, Y_t) of R^2_{++},
outputs y in R^T_{+}.  Mode `strict=False` is weak solvability (cone of weakly reachable sets),
`strict=True` is neoclassical solvability (cone of reachable sets).

Graph: nodes ("src",), ("snk",), ("start", b), ("edge", a, b).  Source-sink paths other than
src -> snk are the strictly convex lower-left chains.  Every arc carries two index sets: Out
(outside the region of the chain) and Bnd (on its boundary).  Theorem (FlowLP.lean,
`mem_indicatorCone_iff_flow`):

    y in cone  <=>  exists a flow f >= 0 and g with
                    y = sum_e f_e 1_{Out e} + g,   0 <= g <= beta * sum_e f_e 1_{Bnd e},

beta = 1 (weak) or 0 (strict).  All combinatorics is computed in exact rationals; the LP is
solved by HiGHS in floating point, and a positive answer is turned into an exact certificate
(`certify`): finitely many sets with rational masses, each set checked reachable exactly by
`is_reachable` (witness intervals, independent of the chain theory).

Change relative to poly-hardness/planar.py: the decision LP `flow_lp` is solved with the interior-point
method (`highs-ipm`), because the polynomiality theorem needs an interior-point method, not simplex.
The exact certificates (`certify`, `_exact_nonneg_solve`) are unchanged.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

SRC, SNK = ("src",), ("snk",)


def frac_points(P):
    return [(Fraction(x), Fraction(y)) for x, y in P]


def cross(P, a, b, q):
    """Positive iff p_q is strictly left of the directed line p_a -> p_b."""
    (xa, ya), (xb, yb), (xq, yq) = P[a], P[b], P[q]
    return (xb - xa) * (yq - ya) - (yb - ya) * (xq - xa)


def down(P, a, b):
    """a -> b can be an edge of a chain: X increases, Y decreases."""
    return P[a][0] < P[b][0] and P[b][1] < P[a][1]


# ---------------------------------------------------------------- slabs (as in FlowLP.lean)


def left_slab(P, b):
    """Left of b (X_q <= X_b), q != b: outside unless on the vertical ray above b."""
    out, bnd = [], []
    for q, (x, y) in enumerate(P):
        if q == b or x > P[b][0]:
            continue
        if x < P[b][0] or y < P[b][1]:
            out.append(q)
        else:
            bnd.append(q)
    return frozenset(out), frozenset(bnd)


def edge_slab(P, a, b):
    """X_a < X_q <= X_b, q != b: outside below the line ab, boundary on it."""
    out, bnd = [], []
    for q, (x, _) in enumerate(P):
        if q == b or not (P[a][0] < x <= P[b][0]):
            continue
        c = cross(P, a, b, q)
        if c < 0:
            out.append(q)
        elif c == 0:
            bnd.append(q)
    return frozenset(out), frozenset(bnd)


def right_slab(P, b):
    """Right of b (X_q > X_b): outside below b, boundary on the horizontal ray."""
    out, bnd = [], []
    for q, (x, y) in enumerate(P):
        if x <= P[b][0]:
            continue
        if y < P[b][1]:
            out.append(q)
        elif y == P[b][1]:
            bnd.append(q)
    return frozenset(out), frozenset(bnd)


@dataclass
class Graph:
    T: int
    nodes: list  # internal nodes, index -> node
    arcs: list  # (tail, head, Out, Bnd); tail/head are nodes


def chain_graph(P) -> Graph:
    """The chain graph of FlowLP.lean (`Node`, `Arc`, `Out`, `Bnd`)."""
    P = frac_points(P)
    T = len(P)
    starts = [("start", b) for b in range(T)]
    edges = [("edge", a, b) for a in range(T) for b in range(T) if down(P, a, b)]
    right = [right_slab(P, b) for b in range(T)]
    arcs = [(SRC, SNK, frozenset(range(T)), frozenset())]
    for node in starts:
        b = node[1]
        arcs.append((SRC, node, *left_slab(P, b)))
        arcs.append((node, SNK, *right[b]))
    for node in edges:
        _, a, b = node
        slab = edge_slab(P, a, b)
        arcs.append((("start", a), node, *slab))
        arcs.append((node, SNK, *right[b]))
    by_tail = {}
    for node in edges:
        by_tail.setdefault(node[1], []).append(node)  # edges a -> b, keyed by a
    for node in edges:
        _, a, b = node
        for nxt in by_tail.get(b, []):
            c = nxt[2]
            if cross(P, a, b, c) > 0:
                arcs.append((node, nxt, *edge_slab(P, b, c)))
    return Graph(T, starts + edges, arcs)


# ---------------------------------------------------------------- the flow LP


@dataclass
class LPResult:
    feasible: bool
    residual: float
    f: np.ndarray  # flow on arcs
    g: np.ndarray  # free boundary part
    w: np.ndarray | None  # Farkas vector (<w, y> < 0, w(S) >= 0 on the family) if infeasible


def flow_lp(P, y, strict: bool = False, graph: Graph | None = None, tol: float = 1e-9):
    """Solve the system of `mem_indicatorCone_iff_flow` with residuals r+, r- in the y rows,
    minimizing their sum.  Zero residual = feasible.  Otherwise the duals of the y rows give a
    Farkas vector w."""
    G = graph or chain_graph(P)
    T, A = G.T, len(G.arcs)
    idx = {node: k for k, node in enumerate(G.nodes)}
    n_int = len(G.nodes)
    beta = 0.0 if strict else 1.0
    # variables: f (A), g (T), r+ (T), r- (T)
    nv = A + 3 * T
    rows, cols, vals = [], [], []
    for k, (u, v, out, _) in enumerate(G.arcs):
        if u in idx:
            rows.append(idx[u])
            cols.append(k)
            vals.append(-1.0)
        if v in idx:
            rows.append(idx[v])
            cols.append(k)
            vals.append(1.0)
        for q in out:
            rows.append(n_int + q)
            cols.append(k)
            vals.append(1.0)
    for q in range(T):
        for j, s in ((A + q, 1.0), (A + T + q, 1.0), (A + 2 * T + q, -1.0)):
            rows.append(n_int + q)
            cols.append(j)
            vals.append(s)
    Aeq = coo_matrix((vals, (rows, cols)), shape=(n_int + T, nv)).tocsr()
    beq = np.concatenate([np.zeros(n_int), np.asarray([float(v) for v in y])])
    rows, cols, vals = [], [], []  # g_q - beta * sum_e f_e [q in Bnd e] <= 0
    for k, (_, _, _, bnd) in enumerate(G.arcs):
        for q in bnd:
            rows.append(q)
            cols.append(k)
            vals.append(-beta)
    for q in range(T):
        rows.append(q)
        cols.append(A + q)
        vals.append(1.0)
    Aub = coo_matrix((vals, (rows, cols)), shape=(T, nv)).tocsr()
    c = np.concatenate([np.zeros(A + T), np.ones(2 * T)])
    res = linprog(c, A_ub=Aub, b_ub=np.zeros(T), A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * nv, method="highs-ipm")
    assert res.status == 0, res.message
    scale = max(1.0, float(np.abs(beq).sum()))
    feasible = res.fun <= tol * scale
    w = None
    if not feasible:
        w = -np.asarray(res.eqlin.marginals[n_int:])  # duals of the y rows, sign flipped
    return LPResult(feasible, res.fun, res.x[:A], res.x[A:A + T], w)


# ---------------------------------------------------------------- column problem


def max_weight(P, w, strict: bool = False, graph: Graph | None = None):
    """max { w(S) : S (weakly) reachable } and a maximizer: a longest path in the chain graph
    with arc weights w(Out e) + beta * sum_{q in Bnd e} max(w_q, 0)."""
    G = graph or chain_graph(P)
    P = frac_points(P)
    w = [Fraction(v) for v in w]

    def weight(out, bnd):
        val = sum((w[q] for q in out), Fraction(0))
        chosen = frozenset() if strict else frozenset(q for q in bnd if w[q] > 0)
        return val + sum((w[q] for q in chosen), Fraction(0)), out | chosen

    def order(node):  # a topological order: src, starts, edges by X of the last vertex, snk
        if node == SRC:
            return (0, 0)
        if node == SNK:
            return (3, 0)
        return (1, 0) if node[0] == "start" else (2, P[node[2]][0])

    best = {SRC: (Fraction(0), frozenset())}
    for u, v, out, bnd in sorted(G.arcs, key=lambda a: order(a[0])):
        if u not in best:
            continue
        val, s = weight(out, bnd)
        cand = (best[u][0] + val, best[u][1] | s)
        if v not in best or cand[0] > best[v][0]:
            best[v] = cand
    return best[SNK]


# ---------------------------------------------------------------- exact checks


def is_reachable(P, S, strict: bool = False) -> bool:
    """Definition check, independent of the chain theory.  t in S needs xi = (th, 1 - th),
    th in [0, 1], with th (X_s - X_t) + (1 - th)(Y_s - Y_t) >= 0 (> 0 if strict) for s not in S:
    an intersection of intervals of th, computed exactly."""
    P = frac_points(P)
    S = set(S)
    rest = [s for s in range(len(P)) if s not in S]
    for t in S:
        lo, lo_open, hi, hi_open = Fraction(0), False, Fraction(1), False
        ok = True
        for s in rest:
            a = P[s][0] - P[t][0]  # value at th = 1
            b = P[s][1] - P[t][1]  # value at th = 0
            # f(th) = b + th (a - b) must be >= 0 (or > 0)
            k = a - b
            if k == 0:
                if b < 0 or (strict and b == 0):
                    ok = False
                    break
                continue
            root = -b / k
            if k > 0:  # th >= root (th > root if strict)
                if root > lo or (root == lo and strict):
                    lo, lo_open = root, strict
            else:  # th <= root
                if root < hi or (root == hi and strict):
                    hi, hi_open = root, strict
        if not ok or lo > hi or (lo == hi and (lo_open or hi_open)):
            return False
    return True


def family(P, strict: bool = False):
    """All (weakly) reachable sets, by brute force over 2^T sets (small T only)."""
    T = len(P)
    return [frozenset(q for q in range(T) if m >> q & 1)
            for m in range(1 << T) if is_reachable(P, [q for q in range(T) if m >> q & 1],
                                                    strict)]


def decompose_flow(G: Graph, f, tol: float = 1e-12):
    """Paths with masses from a flow (greedy: follow positive arcs from the source)."""
    f = np.array(f, dtype=float)
    out_arcs = {}
    for k, (u, *_r) in enumerate(G.arcs):
        out_arcs.setdefault(u, []).append(k)
    paths = []
    while True:
        start = [k for k in out_arcs[SRC] if f[k] > tol]
        if not start:
            return paths
        path, node = [], SRC
        while node != SNK:
            k = max(out_arcs[node], key=lambda j: f[j])
            path.append(k)
            node = G.arcs[k][1]
        m = min(f[k] for k in path)
        for k in path:
            f[k] -= m
        paths.append((m, path))


def _exact_nonneg_solve(cols, y):
    """Solve y = sum_k m_k cols_k, m >= 0, exactly; cols are 0/1 tuples.  Uses a basic
    solution found in floating point, then Gaussian elimination in rationals."""
    if not cols:
        return [] if all(v == 0 for v in y) else None
    M = np.array(cols, dtype=float).T
    res = linprog(np.zeros(len(cols)), A_eq=M, b_eq=[float(v) for v in y],
                  bounds=[(0, None)] * len(cols), method="highs-ds")
    if res.status != 0:
        return None
    support = [k for k in range(len(cols)) if res.x[k] > 1e-12]
    # exact least squares on the support: normal equations, then check the residual
    A = [[Fraction(cols[k][q]) for k in support] for q in range(len(y))]
    n = len(support)
    N = [[sum(A[q][i] * A[q][j] for q in range(len(y))) for j in range(n)] for i in range(n)]
    rhs = [sum(A[q][i] * Fraction(y[q]) for q in range(len(y))) for i in range(n)]
    for i in range(n):  # Gauss-Jordan
        piv = next((r for r in range(i, n) if N[r][i] != 0), None)
        if piv is None:
            return None
        N[i], N[piv], rhs[i], rhs[piv] = N[piv], N[i], rhs[piv], rhs[i]
        for r in range(n):
            if r != i and N[r][i] != 0:
                fct = N[r][i] / N[i][i]
                N[r] = [a - fct * b for a, b in zip(N[r], N[i])]
                rhs[r] -= fct * rhs[i]
    m = [rhs[i] / N[i][i] for i in range(n)]
    if any(v < 0 for v in m):
        return None
    for q in range(len(y)):
        if sum(A[q][i] * m[i] for i in range(n)) != Fraction(y[q]):
            return None
    out = [Fraction(0)] * len(cols)
    for i, k in enumerate(support):
        out[k] = m[i]
    return out


def certify(P, y, strict: bool = False):
    """An exact certificate that y is (weakly) solvable at P: a list of (S, m) with rational
    m >= 0, every S reachable (`is_reachable`), sum m 1_S = y exactly.  None if not found."""
    G = chain_graph(P)
    lp = flow_lp(P, y, strict, G)
    if not lp.feasible:
        return None
    T = G.T
    cand = set()
    bnd_load = np.zeros(T)
    for k, (_, _, _, bnd) in enumerate(G.arcs):
        for q in bnd:
            bnd_load[q] += lp.f[k]
    for _, path in decompose_flow(G, lp.f):
        out = frozenset().union(*(G.arcs[k][2] for k in path))
        bnd = frozenset().union(*(G.arcs[k][3] for k in path))
        cand.add(out)
        if not strict:
            # boundary points with a positive share of g, in the order of the share
            share = sorted((q for q in bnd if lp.g[q] > 1e-12),
                           key=lambda q: -lp.g[q] / bnd_load[q])
            for j in range(1, len(share) + 1):
                cand.add(out | frozenset(share[:j]))
    cand = [S for S in cand if is_reachable(P, S, strict)]
    cols = [tuple(1 if q in S else 0 for q in range(T)) for S in cand]
    m = _exact_nonneg_solve(cols, [Fraction(v) for v in y])
    if m is None:
        return None
    return [(S, mk) for S, mk in zip(cand, m) if mk != 0]


def check_certificate(P, y, cert, strict: bool = False) -> bool:
    """Exact check of a certificate from `certify`."""
    T = len(P)
    total = [Fraction(0)] * T
    for S, m in cert:
        if m < 0 or not is_reachable(P, S, strict):
            return False
        for q in S:
            total[q] += m
    return total == [Fraction(v) for v in y]
