"""Numerical check of the reduction 3-colouring -> (weak) solvability in dimension 3.

For small graphs G it builds the lattice drawing of G box K3 from np-hardness.tex (Section 4) and checks
  * the drawing conditions (Definition 3.1): L <= 16, no node strictly inside the disk with diameter
    an edge, on its circle at most one more node or the two ends of an edge;
  * the colouring lemma (Lemma 5.1): for 3-colourable G the three sets I_tau are independent and
    average to s; for every G an independent set satisfying all tight equalities (one corner per
    triangle, one end of every copy-anticopy edge) exists iff G is 3-colourable (MILP).

Run from the repository root: .venv/bin/python np-hardness/check_layout.py
"""
import itertools

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp


def layout(n, edges):
    """Nodes with positions, values s and owners (vertex, colour, is_copy)."""
    m = len(edges)
    H, pos, s, owner = nx.Graph(), {}, {}, {}
    x0 = lambda i: 3 if i == 1 else 1
    colX = lambda k, i: 24 * k + 8 * i + 8 + (2 if i == 1 else 0)
    for v in range(n):
        for i in range(3):
            for j in range(12 * m + 1):
                p = ('r', v, i, j)
                pos[p], s[p], owner[p] = (x0(i) + 2 * j, 8 * v + 2 * i), (1 / 3 if j % 2 == 0 else 2 / 3), (v, i, j % 2 == 0)
                if j:
                    H.add_edge(('r', v, i, j - 1), p)
        H.add_edges_from([(('r', v, t, 0), ('r', v, (t + 1) % 3, 0)) for t in range(3)])
    for k, (a, b) in enumerate(edges):
        lo, hi = min(a, b), max(a, b)
        N, jA = 4 * (hi - lo), 12 * k
        for i in range(3):
            for j in range(N):
                p = ('c', k, i, j)
                pos[p] = (colX(k, i), 8 * lo + 2 * i + 1 + 2 * j)
                copy = j == 1 or (j % 2 == 0 and j != 0)
                s[p], owner[p] = (1 / 3 if copy else 2 / 3), ((lo if j <= 1 else hi), i, copy)
                if j:
                    H.add_edge(('c', k, i, j - 1), p)
            H.add_edge(('c', k, i, 0), ('r', lo, i, jA + 4 * i + 4))
            H.add_edge(('c', k, i, N - 1), ('r', hi, i, jA + 4 * i + 4))
    assert len(set(pos.values())) == len(pos), "positions not injective"
    return H, pos, s, owner


def drawing_violations(H, pos):
    P = {p: np.array(q) for p, q in pos.items()}
    nodes = list(H.nodes)
    arr = np.array([P[p] for p in nodes])
    bad = 0
    for a, b in H.edges:
        L = int(((P[a] - P[b]) ** 2).sum())
        d = ((2 * arr - P[a] - P[b]) ** 2).sum(1)
        inside = [nodes[k] for k in np.where(d < L)[0]]
        circle = [nodes[k] for k in np.where(d == L)[0] if nodes[k] not in (a, b)]
        ok = L <= 16 and not inside and (len(circle) <= 1 or (len(circle) == 2 and H.has_edge(*circle)))
        bad += not ok
    return bad


def colouring_core(H, s, owner, n, edges):
    col = next((c for c in itertools.product(range(3), repeat=n) if all(c[u] != c[v] for u, v in edges)), None)
    N = list(H.nodes)
    idx = {p: k for k, p in enumerate(N)}
    rows, lo, hi = [], [], []
    for a, b in H.edges:
        r = np.zeros(len(N)); r[idx[a]] = r[idx[b]] = 1
        rows.append(r); lo.append(1 if abs(s[a] + s[b] - 1) < 1e-9 else 0); hi.append(1)
    for v in range(n):
        r = np.zeros(len(N))
        for i in range(3):
            r[idx[('r', v, i, 0)]] = 1
        rows.append(r); lo.append(1); hi.append(1)
    tight = milp(np.zeros(len(N)), constraints=LinearConstraint(np.array(rows), lo, hi),
                 integrality=np.ones(len(N)), bounds=Bounds(0, 1)).status == 0
    average = None
    if col:
        sets = [{p for p in N if ((col[owner[p][0]] + t) % 3 == owner[p][1]) == owner[p][2]} for t in range(3)]
        assert all(not (a in I and b in I) for I in sets for a, b in H.edges)
        average = all(abs(sum(p in I for I in sets) / 3 - s[p]) < 1e-9 for p in N)
    return col is not None, tight, average


GRAPHS = {
    'K2': (2, [(0, 1)]),
    'K3': (3, [(0, 1), (1, 2), (0, 2)]),
    'C5': (5, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]),
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'W5': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)]),
    'Petersen': (10, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
                      (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]),
}

if __name__ == '__main__':
    for name, (n, E) in GRAPHS.items():
        H, pos, s, owner = layout(n, E)
        colourable, tight, average = colouring_core(H, s, owner, n, E)
        print(f'{name:9s} nodes={H.number_of_nodes():5d} drawing violations={drawing_violations(H, pos)} '
              f'3-colourable={colourable} tight independent set={tight} shifts average to s={average}')
