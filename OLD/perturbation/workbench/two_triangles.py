"""Test independence/coupling of pair-cover gadgets."""
import sys
sys.path.insert(0, "/private/tmp/claude-501/-Users-olegoleg-Code-neo-tiling/75c6aa21-1546-4d6f-8f41-0b1e36d1074e/scratchpad")
import numpy as np
from rho_exact import rho_exact

# Single triangle
P1 = np.array([[4, 1], [3, 3], [1, 4]], float); y1 = np.array([1, 5, 3], float)
r1, _, _ = rho_exact(P1, y1, max_fam=3, time_limit=30)
print(f"single triangle rho = {r1:.6f}")

# Two independent triangles (shifted far apart)
P2 = np.vstack([P1, P1 + np.array([100, 100])])
y2 = np.array([1, 5, 3, 1, 5, 3], float)
r2, Q2, F2 = rho_exact(P2, y2, max_fam=5, time_limit=90)
print(f"two independent triangles rho = {r2:.6f} (expected ~{2*r1:.3f})")
print(f"  F = {[sorted(S) for S in (F2 or [])]}")

# Two triangles sharing a vertex? Build on 5 points: triangle (0,1,2) and triangle (2,3,4) sharing index 2
# Triangle 1: p0, p1, p2 on anti-diagonal, p1 above midpoint. 
# Triangle 2: p2, p3, p4 on another anti-diagonal, p3 above midpoint. 
P3 = np.array([[4,1],[3,3],[1,4],[0,3],[-1,0]], float) + np.array([5,5])  # shift to positive
# Hmm this needs more thought. Let me use a careful construction.
# Two sharing a vertex is complex; skip for now.
