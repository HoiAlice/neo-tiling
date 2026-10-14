"""Try an explicit VERTEX COVER reduction. Vertices on anti-diagonal, edges = cover-points at midpoints + eps shift. VC = min cost to resolve all edge-covers."""
import sys, itertools
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
sys.path.insert(0, "/private/tmp/claude-501/-Users-olegoleg-Code-neo-tiling/75c6aa21-1546-4d6f-8f41-0b1e36d1074e/scratchpad")
import numpy as np
from rho_exact import rho_exact

def vc_instance(graph_edges, n, eps=0.1, scale=10):
    """n vertices on anti-diagonal p_v = (scale*v, scale*(n+1-v)).
    For each edge e=(u,v), cover point p_e at midpoint + eps shift."""
    V = n  # vertices
    E = len(graph_edges)
    T = V + E
    P = np.zeros((T, 2))
    for v in range(V):
        P[v] = (scale * (v+1), scale * (V - v))
    for i, (u, v) in enumerate(graph_edges):
        mid = (P[u] + P[v]) / 2
        P[V + i] = mid + np.array([eps, eps])
    # y: ground = 1, cover = 3 (so y_cover > y_u + y_v)
    y = np.ones(T, dtype=float)
    for i in range(E):
        y[V + i] = 3  # or set to make blocking
    return P, y

# K_3: 3 vertices, 3 edges, MIN VC = 2
edges_K3 = [(0, 1), (0, 2), (1, 2)]
P, y = vc_instance(edges_K3, 3, eps=0.5, scale=10)
print("P =", P.tolist(), "y =", y.tolist())
v, Q, F = rho_exact(P, y, max_fam=5, time_limit=60)
print(f"K_3 reduction: rho = {v:.6f}  F = {[sorted(S) for S in F]}")
print(f"  Q = {Q.tolist()}")
# What's the "VC-induced" cost? MIN VC = 2 vertices to cover K_3 (any 2 of 3).
# If each vertex-move costs c_v, moving 2 vertices costs 2 c_v. Edge-moves cost c_e each (3 c_e for all 3).
# We want: optimum = 2 c_v < 3 c_e so VC is preferred.
