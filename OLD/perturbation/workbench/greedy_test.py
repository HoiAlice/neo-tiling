"""Test polynomial candidates for rho_dom.
Candidate: for each conflict, resolve independently (pay min of coord 0 or coord 1 cost).
This is a lower bound. If always matches exact rho_dom, polynomial via greedy."""
import sys, random, itertools
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
sys.path.insert(0, "/private/tmp/claude-501/-Users-olegoleg-Code-neo-tiling/75c6aa21-1546-4d6f-8f41-0b1e36d1074e/scratchpad")
import numpy as np
from iso_scipy import iso_cost
from lp_test import iso_cost_l1

def rho_dom_exact_l1(P, y):
    T = len(P); a = np.log(P[:, 0]); b = np.log(P[:, 1])
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    best = float("inf"); best_sig = None
    for sigma in itertools.product((0, 1), repeat=len(conflicts)):
        e0 = [c for c, s in zip(conflicts, sigma) if s == 0]
        e1 = [c for c, s in zip(conflicts, sigma) if s == 1]
        v = iso_cost_l1(a, e0) + iso_cost_l1(b, e1)
        if v < best - 1e-10: best, best_sig = v, sigma
    return best, best_sig, conflicts

def ind_lb(P, y):
    """Lower bound: for each conflict, min of individual resolution."""
    T = len(P); a = np.log(P[:, 0]); b = np.log(P[:, 1])
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    total = 0
    for t, s in conflicts:
        c0 = max(0, a[t] - a[s])  # L1 cost to flip order on coord 0
        c1 = max(0, b[t] - b[s])
        total += min(c0, c1)
    return total

def dp_rank(P, y):
    """DP by y-rank with Pareto frontier state. Exponential in general, test if poly on small."""
    T = len(P); a = np.log(P[:, 0]); b = np.log(P[:, 1])
    # Process indices in decreasing y order
    order = sorted(range(T), key=lambda t: -y[t])
    # State: a sorted list of (u, v) placed so far (approximately a Pareto frontier)
    # DP is hard to implement cleanly in general; skip for now
    return None

seed, T, N = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed); gaps = []
for k in range(N):
    P = np.array([[rng.randint(1, 10), rng.randint(1, 10)] for _ in range(T)], float)
    y = np.array([rng.randint(0, 5) for _ in range(T)], float)
    if y.max() == 0: continue
    exact, sig, confs = rho_dom_exact_l1(P, y)
    lb = ind_lb(P, y)
    gap = exact - lb
    tag = " GAP" if gap > 1e-5 else ""
    print(f"k={k} T={T} exact={exact:.4f} ind_lb={lb:.4f} gap={gap:.4f}{tag}", flush=True)
    gaps.append(gap)
print(f"\n{sum(1 for g in gaps if g > 1e-5)}/{len(gaps)} gaps; max gap = {max(gaps):.4f}")
