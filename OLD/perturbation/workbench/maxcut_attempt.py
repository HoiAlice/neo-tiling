"""Direct attempt: build small 2-switch pair with specific coupling.
Each 'switch' = 1 conflict (y_t > y_s with p_t dominates p_s).
Shared-vertex gives ferromagnetic coupling (observed).
Antiferromagnetic via chain or pair-cover: investigate."""
import sys, itertools
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
sys.path.insert(0, "/private/tmp/claude-501/-Users-olegoleg-Code-neo-tiling/75c6aa21-1546-4d6f-8f41-0b1e36d1074e/scratchpad")
import numpy as np
from rho_exact import rho_exact
from iso_scipy import rho_dom_fast

# 2-switch sharing a vertex, FERROMAGNETIC (expected)
print("== 2-switch sharing a vertex (ferromagnetic expected)")
# conflict (1,0): y_1>y_0, p_1 dominates p_0.
# conflict (2,0): y_2>y_0, p_2 dominates p_0.
P = np.array([[1, 1], [2, 2], [3, 3]], float); y = np.array([1, 2, 2], float)
val, Q, F = rho_exact(P, y, max_fam=4, time_limit=20)
print(f"rho = {val:.6f}  Q = {Q.tolist() if Q is not None else None}  F = {[sorted(S) for S in (F or [])]}")

# Try antiferromagnetic via chain
print("\n== 3-chain (pure, ferromagnetic prediction)")
P = np.array([[1, 1], [2, 2], [3, 3]], float); y = np.array([1, 2, 3], float)
val, Q, F = rho_exact(P, y, max_fam=4, time_limit=20)
print(f"rho = {val:.6f}  (rho_dom should match)")

# Try pair-cover gadget: triangle-like but with extra points
print("\n== Triangle (pair cover, rho>rho_dom)")
P = np.array([[4, 1], [3, 3], [1, 4]], float); y = np.array([1, 5, 3], float)
val, Q, F = rho_exact(P, y, max_fam=4, time_limit=20)
rd = rho_dom_fast(P, y)[0]
print(f"rho = {val:.6f}  rho_dom = {rd:.6f}  F = {[sorted(S) for S in (F or [])]}")

# Two independent triangles -- cost should be 2x
print("\n== Two independent triangles (far apart)")
# Triangle 1 at scale 1, Triangle 2 shifted by (100, 100)
P1 = np.array([[4, 1], [3, 3], [1, 4]], float)
P2 = P1 + np.array([100, 100])
P = np.vstack([P1, P2])
y = np.array([1, 5, 3, 1, 5, 3], float)
val, Q, F = rho_exact(P, y, max_fam=5, time_limit=60)
print(f"rho = {val:.6f}  (expected ~0.8 if indep, exactly 2x triangle)")
