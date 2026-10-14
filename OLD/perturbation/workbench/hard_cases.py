"""Construct T=4,5 cases with likely rho > rho_dom: embed a 'triangle' obstruction."""
import sys
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from fast_d2 import rho_dom_exact, rho_full_small

# Case A: triangle plus a fourth point far away.
cases = [
    ("triangle + far", np.array([[4,1],[3,3],[1,4],[10,10]], float), np.array([1,5,3,1], float)),
    ("triangle + nearby", np.array([[4,1],[3,3],[1,4],[2,2]], float), np.array([1,5,3,1], float)),
    ("two triangles", np.array([[4,1],[3,3],[1,4],[5,5]], float), np.array([1,5,3,2], float)),
    ("4-point convex", np.array([[1,4],[3,3],[4,1],[2,2]], float), np.array([2,1,2,3], float)),
]

for name, P, y in cases:
    rd = rho_dom_exact(P, y); rf = rho_full_small(P, y, max_family_size=4)
    print(f"{name:25s} T={len(P)} rho={rf.rho:.6f} rho_dom={rd.rho:.6f} gap={rf.rho-rd.rho:+.6f}  sigma={rd.sigma}  conflicts={rd.conflicts}  family={[sorted(S) for S in (rf.family or [])]}", flush=True)
