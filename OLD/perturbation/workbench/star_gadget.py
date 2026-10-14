"""Star gadget: 1 center, 3 leaves. Try to make all-same expensive, NAE cheap."""
import sys, itertools, random
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from iso_scipy import iso_cost

def star_sigma_costs(center, leaves):
    """Center at (xc, yc) with y_c large; leaves at positions with y_l = equal (lower).
    Only conflicts: (0, i+1) for i = 0, 1, 2. 3 conflicts, 8 sigma patterns."""
    P = np.array([center] + list(leaves), float)
    y = np.array([3.0, 1.0, 1.0, 1.0], float)
    conflicts = [(0, 1), (0, 2), (0, 3)]
    a = [np.log(P[:, 0]), np.log(P[:, 1])]
    results = []
    for sigma in itertools.product((0, 1), repeat=3):
        edges = [[], []]
        for (t, s), i in zip(conflicts, sigma):
            edges[i].append((t, s))
        c0, _ = iso_cost(a[0], edges[0])
        c1, _ = iso_cost(a[1], edges[1])
        results.append((sigma, c0, c1, c0 + c1))
    return results, conflicts

print("== Symmetric star: all leaves equal, center at (10, 10)")
res, _ = star_sigma_costs([10, 10], [[1, 1]] * 3)
for sigma, c0, c1, tot in sorted(res, key=lambda r: r[3]):
    tag = "  SAME" if all(x == sigma[0] for x in sigma) else "  NAE"
    print(f"  sigma={sigma} tot={tot:.3f}{tag}")

print("\n== Anisotropic star: center at (10, 10), leaves (a, b) with varying a, b")
# One leaf cheap on coord 0 only, one cheap on coord 1 only, one balanced
res, _ = star_sigma_costs([10, 10], [[1, 10], [10, 1], [1, 1]])
for sigma, c0, c1, tot in sorted(res, key=lambda r: r[3]):
    tag = "  SAME" if all(x == sigma[0] for x in sigma) else "  NAE"
    print(f"  sigma={sigma} c0={c0:.3f} c1={c1:.3f} tot={tot:.3f}{tag}")

print("\n== Searching anisotropic star configurations for NAE-like gap")
random.seed(1); best = None
for trial in range(300):
    center = [random.uniform(5, 20), random.uniform(5, 20)]
    leaves = [[random.uniform(0.5, 5), random.uniform(0.5, 5)] for _ in range(3)]
    res, _ = star_sigma_costs(center, leaves)
    same_cost = min(c for s, _, _, c in res if all(x == s[0] for x in s))
    nae_cost  = min(c for s, _, _, c in res if not all(x == s[0] for x in s))
    gap = same_cost - nae_cost
    if best is None or gap > best[0]:
        best = (gap, same_cost, nae_cost, center, leaves, res)

gap, sc, nc, center, leaves, res = best
print(f"best gap = {gap:.3f}  same = {sc:.3f}  nae = {nc:.3f}")
print(f"center={center} leaves={leaves}")
for sigma, c0, c1, tot in sorted(res, key=lambda r: r[3]):
    tag = "  SAME" if all(x == sigma[0] for x in sigma) else "  NAE"
    print(f"  sigma={sigma} tot={tot:.3f}{tag}")
