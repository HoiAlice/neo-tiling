"""Try K_4: 4 switches, all pairs antiferromagnetic. Enumerate 2^12 patterns."""
import sys, itertools, time
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/scratchpad/gad")
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from iso_scipy import iso_cost

def switch(cx, cy, d):
    """Returns 2 points: top (cx+d, cy+d), bottom (cx, cy); their grid positions."""
    return [(cx + d, cy + d), (cx, cy)]

def enum_rho(P, y, max_sigma=4096):
    T = len(P); a = [np.log(P[:, 0]), np.log(P[:, 1])]
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    nc = len(conflicts)
    if 2 ** nc > max_sigma:
        print(f"too many conflicts ({nc})"); return None
    best = float("inf"); best_s = None
    for sigma in itertools.product((0, 1), repeat=nc):
        e = [[], []]
        for (t, s), i in zip(conflicts, sigma): e[i].append((t, s))
        c0 = iso_cost(a[0], e[0])[0]; c1 = iso_cost(a[1], e[1])[0]
        if c0 + c1 < best - 1e-10: best, best_s = c0 + c1, sigma
    return best, best_s, conflicts

# K_4 attempt: 4 switches at anti-chain positions. All pairs should have ox*oy < 0.
# Try: switch centers at (0,10), (10,0), (20,-10)... hmm must be on antichain.
# Antichain of 4 points: no two comparable. E.g., (0, 3), (1, 2), (2, 1), (3, 0).
d = 4
centers = [(0, 3), (1, 2), (2, 1), (3, 0)]  # scaled by what factor?
scale = 5  # multiply so offsets are >= 3 for antiferro to kick in
centers = [(scale * c[0], scale * c[1]) for c in centers]
P_grid = []; y = []
for c in centers:
    tops_bots = switch(c[0], c[1], d)
    P_grid += tops_bots
    y += [2, 1]
P = np.exp(0.2 * np.array(P_grid))  # same scaling as agent
y = np.array(y, float)
t0 = time.time()
r = enum_rho(P, y)
print(f"K_4 attempt (centers {centers} d={d}): rho_dom = {r[0]:.5f} sigma = {r[1]}  time {time.time()-t0:.1f}s")
# Count "pairwise agreement" in sigma for just the 4 main switch conflicts
# Main switch conflicts: (0,1), (2,3), (4,5), (6,7)? Depends on switch indices...
