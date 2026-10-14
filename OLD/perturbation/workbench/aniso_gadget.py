"""Try to design a 3-conflict NAE gadget with anisotropic costs."""
import sys, itertools
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from iso_scipy import iso_cost

def enum_sigmas(P, y):
    T = len(P)
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    a = [np.log(P[:, 0]), np.log(P[:, 1])]
    rows = []
    for sigma in itertools.product((0, 1), repeat=len(conflicts)):
        edges = [[], []]
        for (t, s), i in zip(conflicts, sigma):
            edges[i].append((t, s))
        c0, _ = iso_cost(a[0], edges[0])
        c1, _ = iso_cost(a[1], edges[1])
        rows.append((sigma, c0, c1, c0 + c1))
    rows.sort(key=lambda r: r[3])
    return conflicts, rows

# Anisotropic 3-chain attempt: points with cost expensive on one coord, cheap on other.
# For NAE want: all-same σ expensive, mixed σ cheap.

tries = [
    # Points where moving coord 0 is cheap for 1, expensive for 2; opposite for coord 1
    ("A", np.array([[1, 1], [2, 10], [10, 2]], float), np.array([1, 2, 3], float)),
    ("B", np.array([[1, 1], [1.1, 5], [5, 1.1]], float), np.array([1, 2, 3], float)),
    ("C", np.array([[1, 1], [3, 1.5], [1.5, 3]], float), np.array([1, 3, 2], float)),  # y order different
    ("D", np.array([[1, 1], [10, 1.1], [1.1, 10]], float), np.array([1, 3, 2], float)),
    # try two conflicts only
    ("E", np.array([[1, 1], [10, 1.1], [1.1, 10]], float), np.array([1, 2, 2], float)),
]

for name, P, y in tries:
    conflicts, rows = enum_sigmas(P, y)
    print(f"\n== {name}: P={P.tolist()} y={y.tolist()} conflicts={conflicts}")
    for sigma, c0, c1, tot in rows[:4]:
        samecol = all(x == sigma[0] for x in sigma)
        tag = " ALL-SAME" if samecol else ""
        print(f"   sigma={sigma} c0={c0:.4f} c1={c1:.4f} tot={tot:.4f}{tag}")
    for sigma, c0, c1, tot in rows[-2:]:
        samecol = all(x == sigma[0] for x in sigma)
        tag = " ALL-SAME" if samecol else ""
        print(f"   sigma={sigma} c0={c0:.4f} c1={c1:.4f} tot={tot:.4f}{tag}")
