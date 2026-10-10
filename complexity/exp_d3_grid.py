"""Experiment: the drawing lemma on K4.

Orthogonal grid drawing of K4 (scaled by 4), every edge path subdivided at the integer points
except that the first two units of its first segment are cut into three pieces of length 2/3.
Checks exactly: all points in (1/3)Z^2, every new edge Gabriel with margin >= 1/9 (grid units),
an even number of subdivision vertices per edge, and alpha(G'') = alpha(G) + sum L_e / 2
(MILP).  Then normalizes into the box |a0|+|a1| <= 1/8 and checks the hypotheses of the Lean
theorem mem_indicatorCone_iff_inStab_of_gabriel."""
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

from d3_reduction import gabriel_margin, normalize

# K4: A(0,4) B(4,8) C(8,4) D(4,0); polylines (multiples of 4 after scaling)
V = {"A": (0, 4), "B": (4, 8), "C": (8, 4), "D": (4, 0)}
paths = {
    ("A", "B"): [(0, 4), (0, 8), (4, 8)],
    ("B", "C"): [(4, 8), (8, 8), (8, 4)],
    ("C", "D"): [(8, 4), (8, 0), (4, 0)],
    ("D", "A"): [(4, 0), (0, 0), (0, 4)],
    ("A", "C"): [(0, 4), (8, 4)],
    ("B", "D"): [(4, 8), (4, 12), (12, 12), (12, -4), (4, -4), (4, 0)],
}
S = 4
pts, idx, edges = [], {}, []


def pid(p):
    if p not in idx:
        idx[p] = len(pts)
        pts.append(p)
    return idx[p]


for name, p in V.items():
    pid((Fr(p[0] * S), Fr(p[1] * S)))
Ltot = 0
for (u, w), poly in paths.items():
    poly = [(Fr(x * S), Fr(y * S)) for x, y in poly]
    seq = [poly[0]]
    for si, (p, q) in enumerate(zip(poly, poly[1:])):
        L = int(abs(q[0] - p[0]) + abs(q[1] - p[1]))
        assert L % 4 == 0 and L > 0
        dx, dy = (q[0] - p[0]) / L, (q[1] - p[1]) / L
        steps = [Fr(2, 3), Fr(4, 3)] + list(range(2, L + 1)) if si == 0 else range(1, L + 1)
        seq += [(p[0] + dx * t, p[1] + dy * t) for t in steps]
    Ltot += sum(int(abs(q[0] - p[0]) + abs(q[1] - p[1])) for p, q in zip(poly, poly[1:]))
    ids = [pid(p) for p in seq]
    assert (len(ids) - 2) % 2 == 0, "odd number of subdivision vertices"
    edges += list(zip(ids, ids[1:]))

g = gabriel_margin(pts, edges)
print("vertices", len(pts), "edges", len(edges), "Gabriel margin (grid units)", g, ">= 1/9:", g >= Fr(1, 9))
assert all((3 * x).denominator == 1 and (3 * y).denominator == 1 for x, y in pts)

# alpha via MILP
n = len(pts)
A = np.zeros((len(edges), n))
for k, (u, v) in enumerate(edges):
    A[k, u] = A[k, v] = 1
res = milp(-np.ones(n), constraints=LinearConstraint(A, -np.inf, 1), integrality=np.ones(n),
           bounds=Bounds(0, 1))
alpha = round(-res.fun)
print("alpha(G'') =", alpha, " alpha(K4) + Ltot/2 =", 1 + Ltot // 2)

A01 = normalize(pts)
gam = gabriel_margin(A01, edges)
print("after normalization: box ok", all(abs(a) + abs(b) <= Fr(1, 8) for a, b in A01),
      " gamma =", gam, " gamma <= 1/2:", gam <= Fr(1, 2),
      " distinct endpoints:", all(A01[u] != A01[v] for u, v in edges))
