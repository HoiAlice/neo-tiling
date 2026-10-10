"""Polynomial weak-solvability test for d = 2 (compact flow LP).

Let U be the complement of a weakly reachable set S.  U is closed: no point outside U lies in
int C(U), C(U) := conv(p_U) + R^2_+.  For U != {} the set C(U) is
    { (x, y) : x >= x_1, y >= phi(x) },
where v_1, ..., v_k (indices in U) are the vertices of the lower-left convex chain of p_U:
x strictly increasing, y strictly decreasing, slopes strictly increasing; phi is the chain on
[x_1, x_k] and the constant y_k to the right.  Its interior is {x > x_1, y > phi(x)}.

Every other index q falls into exactly one vertical "piece" of the chain:
  left  piece  of v_1          : x_q <= x_1
  edge  piece  of (v_j, v_j+1) : x_j < x_q <= x_j+1
  right piece  of v_k          : x_q > x_k
and its status (OUT of C, on the BOUNDARY of C, or INTERIOR) depends only on that piece.
Interior points must be in U, OUT points must be in S, boundary points are free.  Conversely
any chain with any choice of boundary points gives a closed U.  So
    cone(F) = { sum_paths m_V (1_OUT(V) + z_V) : 0 <= z_V <= 1_BND(V) },
and OUT, BND are sums of per-node contributions along a path in a DAG whose nodes are
"first vertex a" and "last edge (a, b)".  This gives an LP with O(T^3) arcs.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

OUT, BND, INT = 0, 1, 2


def _cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


@dataclass
class Dag:
    T: int
    nodes: list = field(default_factory=list)  # ("A", a) | ("E", a, b)
    out: list = field(default_factory=list)  # per node: list of OUT indices of its piece
    bnd: list = field(default_factory=list)  # per node: list of BND indices
    arcs: list = field(default_factory=list)  # (u, v, out_extra, bnd_extra); u/v = -1 src, -2 sink


def left_piece(P, a):
    xa, ya = P[a]
    out, bnd = [], []
    for q, (x, y) in enumerate(P):
        if q == a or x > xa:
            continue
        if x < xa or y < ya:
            out.append(q)
        else:
            bnd.append(q)
    return out, bnd


def edge_piece(P, a, b):
    out, bnd = [], []
    xa, xb = P[a][0], P[b][0]
    for q, p in enumerate(P):
        if q == b or not (xa < p[0] <= xb):
            continue
        c = _cross(P[a], P[b], p)  # > 0 : above the line (x increasing from a to b)
        if c < 0:
            out.append(q)
        elif c == 0:
            bnd.append(q)
    return out, bnd


def right_piece(P, v):
    xv, yv = P[v]
    out, bnd = [], []
    for q, (x, y) in enumerate(P):
        if x <= xv:
            continue
        if y < yv:
            out.append(q)
        elif y == yv:
            bnd.append(q)
    return out, bnd


def build_dag(P) -> Dag:
    T = len(P)
    P = [tuple(Fraction(c) for c in p) for p in P]
    g = Dag(T)
    idx = {}
    for a in range(T):
        idx["A", a] = len(g.nodes)
        g.nodes.append(("A", a))
        o, b_ = left_piece(P, a)
        g.out.append(o)
        g.bnd.append(b_)
    for a in range(T):
        for b in range(T):
            if P[b][0] > P[a][0] and P[b][1] < P[a][1]:
                idx["E", a, b] = len(g.nodes)
                g.nodes.append(("E", a, b))
                o, b_ = edge_piece(P, a, b)
                g.out.append(o)
                g.bnd.append(b_)
    right = [right_piece(P, v) for v in range(T)]
    # arcs
    g.arcs.append((-1, -2, list(range(T)), []))  # U = {} : S = [T]
    for a in range(T):
        g.arcs.append((-1, idx["A", a], [], []))
        g.arcs.append((idx["A", a], -2, *right[a]))
    for key, u in idx.items():
        if key[0] != "E":
            continue
        _, a, b = key
        if ("A", a) in idx:
            g.arcs.append((idx["A", a], u, [], []))
        g.arcs.append((u, -2, *right[b]))
        for c in range(T):
            k2 = ("E", b, c)
            if k2 in idx and _cross(P[a], P[b], P[c]) > 0:
                g.arcs.append((u, idx[k2], [], []))
    return g


def _incidence(g: Dag):
    """Per-arc OUT and BND vectors (node pieces are charged on arcs entering the node)."""
    n_arcs = len(g.arcs)
    O = lil_matrix((g.T, n_arcs))
    B = lil_matrix((g.T, n_arcs))
    for k, (u, v, oe, be) in enumerate(g.arcs):
        outs = list(oe) + (g.out[v] if v >= 0 else [])
        bnds = list(be) + (g.bnd[v] if v >= 0 else [])
        for q in outs:
            O[q, k] += 1
        for q in bnds:
            B[q, k] += 1
    return O.tocsr(), B.tocsr()


def weakly_solvable_2d(P, y, tol: float = 1e-9, strict: bool = False) -> bool:
    """LP: flow f on the DAG (free value), slack g;
    y = O f + g,  0 <= g <= B f,  conservation at every internal node.
    strict=True tests solvability (reachable sets): boundary points then belong to the
    complement, so g = 0."""
    g = build_dag(P)
    T, nA, nN = g.T, len(g.arcs), len(g.nodes)
    O, B = _incidence(g)
    if strict:
        B = B * 0
    y = np.asarray([float(v) for v in y])
    # variables: f (nA), gslack (T), r+ (T), r- (T)
    nv = nA + 3 * T
    Aeq = lil_matrix((nN + T, nv))
    for k, (u, v, *_ ) in enumerate(g.arcs):
        if u >= 0:
            Aeq[u, k] -= 1
        if v >= 0:
            Aeq[v, k] += 1
    Ofull = O.toarray()
    for q in range(T):
        for k in np.nonzero(Ofull[q])[0]:
            Aeq[nN + q, k] = Ofull[q, k]
        Aeq[nN + q, nA + q] = 1
        Aeq[nN + q, nA + T + q] = 1
        Aeq[nN + q, nA + 2 * T + q] = -1
    beq = np.concatenate([np.zeros(nN), y])
    Aub = lil_matrix((T, nv))  # g - B f <= 0
    Bfull = B.toarray()
    for q in range(T):
        for k in np.nonzero(Bfull[q])[0]:
            Aub[q, k] = -Bfull[q, k]
        Aub[q, nA + q] = 1
    c = np.concatenate([np.zeros(nA + T), np.ones(2 * T)])
    res = linprog(c, A_ub=Aub.tocsr(), b_ub=np.zeros(T), A_eq=Aeq.tocsr(), b_eq=beq,
                  bounds=[(0, None)] * nv, method="highs")
    assert res.status == 0, res.message
    return res.fun <= tol * max(1.0, float(np.abs(y).sum()))


def solvable_2d(P, y, tol: float = 1e-9) -> bool:
    """Solvability (cone of reachable sets) for d = 2."""
    return weakly_solvable_2d(P, y, tol, strict=True)


def max_weight_2d(P, w, strict: bool = False) -> Fraction:
    """Column problem max_{S (weakly) reachable} w(S): longest path in the DAG."""
    g = build_dag(P)
    w = [Fraction(v) for v in w]

    def val(outs, bnds):
        if strict:
            bnds = ()
        return sum((w[q] for q in outs), Fraction(0)) + sum((max(w[q], 0) for q in bnds),
                                                            Fraction(0))

    # topological order: A-nodes, then E-nodes by x of the second vertex (x strictly increases)
    P2 = [tuple(Fraction(c) for c in p) for p in P]

    def key(n):
        node = g.nodes[n]
        return (0, 0) if node[0] == "A" else (1, P2[node[2]][0])

    order = sorted(range(len(g.nodes)), key=key)
    out_arcs = {}
    for (u, v, oe, be) in g.arcs:
        out_arcs.setdefault(u, []).append((v, oe, be))
    best = {n: None for n in range(len(g.nodes))}
    sink = None

    def relax(v, value):
        nonlocal sink
        if v == -2:
            sink = value if sink is None else max(sink, value)
        elif best[v] is None or value > best[v]:
            best[v] = value

    for v, oe, be in out_arcs[-1]:
        relax(v, val(oe, be) + (val(g.out[v], g.bnd[v]) if v >= 0 else 0))
    for n in order:
        if best[n] is None:
            continue
        for v, oe, be in out_arcs.get(n, []):
            relax(v, best[n] + val(oe, be) + (val(g.out[v], g.bnd[v]) if v >= 0 else 0))
    return sink


def enumerate_family_2d(P, strict: bool = False) -> set[frozenset[int]]:
    """All sets produced by DAG paths with all boundary choices (small T only).
    strict=True: boundary points go to the complement (reachable sets)."""
    g = build_dag(P)
    out_arcs = {}
    for (u, v, oe, be) in g.arcs:
        out_arcs.setdefault(u, []).append((v, oe, be))
    fam = set()

    def dfs(u, outs, bnds):
        for v, oe, be in out_arcs.get(u, []):
            o2 = outs | set(oe) | (set(g.out[v]) if v >= 0 else set())
            b2 = bnds | set(be) | (set(g.bnd[v]) if v >= 0 else set())
            if v == -2:
                bl = [] if strict else sorted(b2)
                for m in range(1 << len(bl)):
                    fam.add(frozenset(o2 | {bl[i] for i in range(len(bl)) if m >> i & 1}))
            else:
                dfs(v, o2, b2)

    dfs(-1, frozenset(), frozenset())
    return fam
