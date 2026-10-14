"""K_4: 4 antichain points all within |Δ|_inf < d so all 6 pairs are antiferro."""
import sys, itertools, time
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from iso_scipy import iso_cost

def enum_rho(P, y, max_sigma=70000):
    T = len(P); a = [np.log(P[:, 0]), np.log(P[:, 1])]
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    nc = len(conflicts)
    if 2 ** nc > max_sigma: return None
    best = float("inf"); best_s = None
    for sigma in itertools.product((0, 1), repeat=nc):
        e = [[], []]
        for (t, s), i in zip(conflicts, sigma): e[i].append((t, s))
        c0 = iso_cost(a[0], e[0])[0]; c1 = iso_cost(a[1], e[1])[0]
        if c0 + c1 < best - 1e-10: best, best_s = c0 + c1, sigma
    return best, best_s, conflicts

# K_4: switches at (0,3), (1,2), (2,1), (3,0) with gap d.
# Switch i has top (c+d, c+d), bottom (c, c).
d = 4; centers = [(0, 3), (1, 2), (2, 1), (3, 0)]
P_grid = []; y = []
for c in centers:
    P_grid.append((c[0] + d, c[1] + d)); y.append(2)
    P_grid.append((c[0], c[1])); y.append(1)
P = np.exp(0.2 * np.array(P_grid, float))
y = np.array(y, float)
t0 = time.time()
r = enum_rho(P, y)
print(f"K_4 (centers {centers}, d={d}): rho_dom = {r[0]:.5f}  time {time.time()-t0:.1f}s")
# Baseline: 4 switches independent cost 4 * B1 ≈ 3.9346
# K_4 all antiferro = can we 2-color 4 vertices avoiding all monochromatic edges? NO (K_4 not bipartite).
# So MIN unsatisfied = at least 3 in a triangle = 2.
# Expected: 4*B1 + 2*J ≈ 3.93 + 0.42 = 4.35
print(f"  baseline 4*B1 = {4 * 0.98365:.4f}")

# Now also enumerate "switch sigma per switch" (bit per switch, 2^4 = 16 options)
# For each bit assignment, compute cost (optimal sigma for internal conflicts given bits)
best_sw = float("inf"); best_bits = None
a_arr = [np.log(P[:, 0]), np.log(P[:, 1])]
conflicts = [(t, s) for t in range(len(P)) for s in range(len(P)) if y[t] > y[s]]
for bits in itertools.product((0, 1), repeat=4):
    # Switch k has top at index 2k, bottom at 2k+1. "Bit = 0" means σ for internal conflict (2k, 2k+1) = 0.
    # Internal conflict indices in `conflicts` list: find them.
    fixed = {}
    for k in range(4):
        idx = conflicts.index((2 * k, 2 * k + 1))
        fixed[idx] = bits[k]
    # Enumerate other sigmas
    other_idx = [i for i in range(len(conflicts)) if i not in fixed]
    best_in = float("inf")
    for rest in itertools.product((0, 1), repeat=len(other_idx)):
        sig = list(fixed[i] if i in fixed else None for i in range(len(conflicts)))
        for j, idx in enumerate(other_idx):
            sig[idx] = rest[j]
        sig = tuple(sig)
        e = [[], []]
        for (t, s), i in zip(conflicts, sig): e[i].append((t, s))
        c0 = iso_cost(a_arr[0], e[0])[0]; c1 = iso_cost(a_arr[1], e[1])[0]
        if c0 + c1 < best_in - 1e-10: best_in = c0 + c1
    if best_in < best_sw: best_sw, best_bits = best_in, bits
    print(f"  bits = {bits}: min cost = {best_in:.5f}")
print(f"best bits = {best_bits} cost = {best_sw:.5f}")
