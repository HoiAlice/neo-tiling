"""Search for T=3 configurations with NAE preference: min-cost sigma is nonconstant,
AND min over constant sigmas is strictly larger than min over NAE sigmas by a margin."""
import sys, random, itertools
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from iso_scipy import iso_cost

def eval_all(P, y):
    T = len(P)
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    if len(conflicts) != 3: return None
    a = [np.log(P[:, 0]), np.log(P[:, 1])]
    best_same = best_nae = np.inf
    best_nae_sigma = None
    for sigma in itertools.product((0, 1), repeat=3):
        edges = [[], []]
        for (t, s), i in zip(conflicts, sigma):
            edges[i].append((t, s))
        c0, _ = iso_cost(a[0], edges[0])
        c1, _ = iso_cost(a[1], edges[1])
        tot = c0 + c1
        if all(x == sigma[0] for x in sigma):
            best_same = min(best_same, tot)
        else:
            if tot < best_nae: best_nae, best_nae_sigma = tot, sigma
    return conflicts, best_same, best_nae, best_nae_sigma

random.seed(42); hits = 0
for trial in range(200):
    P = np.array([[random.uniform(1, 10), random.uniform(1, 10)] for _ in range(3)], float)
    y = np.array([random.randint(1, 3) for _ in range(3)], float)
    res = eval_all(P, y)
    if res is None: continue
    conflicts, bs, bn, sig = res
    gap = bs - bn
    if gap > 0.5 and bn < 10:
        hits += 1
        if hits <= 5:
            print(f"NAE hit: P={P.round(2).tolist()} y={y.tolist()} conf={conflicts} same={bs:.3f} NAE={bn:.3f} sigma={sig}")
print(f"\n{hits}/200 trials showed NAE gap > 0.5 with finite min")
