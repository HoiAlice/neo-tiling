"""Fast sweep: random d=2 instances, compute rho_dom only (fast). Check structure."""
import sys, random, json
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from iso_scipy import rho_dom_fast

def rand(T, rng, grid):
    while True:
        P = np.array([[rng.randint(1, grid), rng.randint(1, grid)] for _ in range(T)], float)
        y = np.array([rng.randint(0, 5) for _ in range(T)], float)
        if y.max() > 0 and y.min() < y.max(): return P, y

def check_rank_mono(sigma, conflicts, y):
    """Rank-monotone: if (t, s) -> coord i and y_t > y_t' > y_s' > y_s, then (t', s') -> i too."""
    rank = {t: int(np.sum(y > y[t]) + np.sum((y == y[t]) & (np.arange(len(y)) < t))) for t in range(len(y))}
    assign = {c: s for c, s in zip(conflicts, sigma)}
    for (t, s), i in zip(conflicts, sigma):
        rt, rs = rank[t], rank[s]
        for t2 in range(len(y)):
            for s2 in range(len(y)):
                if (t2, s2) in assign and rank[t] <= rank[t2] < rank[s2] <= rank[s] and assign[(t2, s2)] != i and (t, s) != (t2, s2):
                    return False
    return True

seed, T, N, grid = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 5
rng = random.Random(seed)
mono = tot = 0; rows = []
for k in range(N):
    P, y = rand(T, rng, grid)
    val, sigma, conflicts, Q = rho_dom_fast(P, y)
    if sigma is None: continue
    tot += 1
    rm = check_rank_mono(sigma, conflicts, y)
    mono += rm
    print(f"k={k} T={T} nconf={len(conflicts)} rho_dom={val:.6f} sigma={sigma} rank-mono={rm}", flush=True)
    rows.append(dict(k=k, P=P.tolist(), y=y.tolist(), rho_dom=val, sigma=sigma, conflicts=conflicts, rank_mono=rm))
print(f"\n== T={T} grid={grid}: {mono}/{tot} rank-monotone")
with open(f"/private/tmp/claude-501/-Users-olegoleg-Code-neo-tiling/75c6aa21-1546-4d6f-8f41-0b1e36d1074e/scratchpad/fast_T{T}_s{seed}_g{grid}.json", "w") as f:
    json.dump(rows, f)
