"""Test: is 2-level rho_dom at d=2 polynomial via staircase DP?

Setup: y has 2 values H (heavy) and L (light), H > 2L > 0. A set S is weakly
reachable iff S^c forms a convex down-set K (i.e. no heavy point of S strictly
dominates a light-point convex combination from S^c). Simpler characterisation:
drop a heavy to below conv(L) \\ or move lights up to the heavy.

For 2 levels (y in {H, L}), rho_dom is the min cost to make it so that no heavy
strictly dominates any light. (The convex-combination constraint, i.e. the
pair-cover, is the extra bit for full rho.)

So for ANTI-DOM-2 (2-level): we have H heavy points and L light points. We can
move anyone in 2D (log coord L1 for simplicity here) such that for every (h, l),
not (h.x > l.x AND h.y > l.y).

Here we fit it as a disjunctive LP, enumerate for small instances, and compare
with a candidate DP based on nested staircases.
"""
import sys, itertools, random
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from iso_scipy import iso_cost


def anti_dom_2_brute(H, L):
    """Enumerate sigma (per heavy-light pair, which coord satisfies).
    Returns min L1 cost of moving to satisfy all pairs. In log coord.
    """
    nH, nL = len(H), len(L)
    pairs = [(h, l) for h in range(nH) for l in range(nL)]
    nc = len(pairs)
    if 2 ** nc > 2 ** 20: return None  # too big
    aH = [np.log(H[:, 0]), np.log(H[:, 1])]
    aL = [np.log(L[:, 0]), np.log(L[:, 1])]
    best = float("inf")
    for sigma in itertools.product((0, 1), repeat=nc):
        # sigma = 0 => coord 0 constraint: H.x <= L.x
        # sigma = 1 => coord 1 constraint: H.y <= L.y
        # Build constraint lists per coord. Edges: (heavy_idx, light_idx)
        # We need u_heavy <= u_light where u = log of coord
        e0 = []; e1 = []
        for (h, l), s in zip(pairs, sigma):
            if s == 0: e0.append((h, l + nH))
            else: e1.append((h, l + nH))
        # iso_cost takes array a and edges (i, j) meaning u_i <= u_j
        a0 = np.concatenate([aH[0], aL[0]])
        a1 = np.concatenate([aH[1], aL[1]])
        c0 = iso_cost(a0, e0)[0]
        c1 = iso_cost(a1, e1)[0]
        if c0 + c1 < best - 1e-10:
            best = c0 + c1
    return best


def anti_dom_2_staircase_dp(H, L):
    """Candidate DP: enumerate staircases separating H from L in 2D (log coords).
    A staircase is a monotone step function; parametrized by its (x, y) breakpoints.
    For each staircase, pay movement costs: H points above should move below (L1),
    L points below should move above.

    Specifically: a staircase is defined by: which heavies are "below" (moved to
    bottom-left of staircase) and which lights are "above" (moved to top-right).
    Actually, the simplest formulation: pick a chain of (x_t, y_t) breakpoints
    for the staircase; H must be below or left of staircase (equivalently, each H
    is to the SW of some staircase vertex), L must be above or right.

    We discretize to the point grid: candidate x-coords = sorted log-H-x and log-L-x,
    similarly for y. There are O(n^2) staircases if monotone chain through grid.
    """
    # Build grid
    nH, nL = len(H), len(L)
    all_pts = np.vstack([H, L])
    xs = sorted(set(np.log(all_pts[:, 0]).tolist()))
    ys = sorted(set(np.log(all_pts[:, 1]).tolist()))
    nx, ny = len(xs), len(ys)
    # Staircase: for each x-strip, a y threshold. H in strip must be below threshold,
    # L in strip must be above threshold.
    # Enumerate thresholds as a decreasing function of x (staircase descending).
    # Represented by: y-rank for each x (0..ny), with y_rank non-increasing (threshold goes down).
    # Cost per H in strip at (x, y_h): max(0, y_h - threshold_y) in log1 coord...
    # Actually: H must have log y <= threshold. If log y > threshold, cost = log y - threshold.
    # Similarly, H must have log x <= threshold_x; but we have per-strip definition.
    #
    # Hmm let me redefine. Staircase in 2D = monotone non-increasing step curve:
    # for each x, the max y such that (x,y) is in the LOW region. H should be in LOW,
    # L should be in HIGH region.
    #
    # Given a staircase y = f(x) (f non-increasing), cost = sum over H: if H not in LOW
    # (H.x > rightmost x where f(x) >= H.y, or H.y > f(H.x)), pay L1 distance to boundary;
    # similarly for L.
    #
    # This is non-trivial but polynomial. The DP state: breakpoint (x_i, y_j), and we
    # move the staircase from top-left to bottom-right.
    #
    # For simplicity here, enumerate ALL monotone staircases on the (nx+1)*(ny+1) grid.
    # Each staircase = sequence of (x_1, y_1), (x_2, y_2), ... with x increasing, y non-increasing.
    # Equivalently: a path from (0, ny) to (nx, 0) in a grid, going right or down only.
    #
    # Enumerate all such paths; cost of each path; min.
    def cost_of_staircase(path):
        # path: list of (xi, yi) with x increasing and y non-increasing,
        # starting at (0, ny) ending at (nx, 0). Converts to piecewise constant threshold.
        # In log coords, staircase y threshold at x in (xs[path[i].xi], xs[path[i+1].xi]) = ys[path[i].yi]
        # Simpler: for each point, decide its region.
        # LOW region = below staircase: (log_x, log_y) with log_y <= threshold(log_x).
        # Build threshold function from path.
        # path is list of (xi, yi) corners; threshold is step: between corner i and i+1,
        # threshold = ys[yi_i] (assuming corner is top-left of step).
        total = 0.0
        for (hx, hy) in np.log(H):
            # Find threshold at hx: last corner with xs[xi] <= hx
            thr = float('inf')
            for (xi, yi) in path:
                if xs[xi] <= hx: thr = ys[yi] if yi < ny else float('inf')
                else: break
            # H must be in LOW: hy <= thr. If not, pay (hy - thr).
            if hy > thr: total += hy - thr
            # Also H.x constraint: need hx <= rightmost x in path where threshold applies?
            # Actually in disjunctive form, we need: for each (h, l) pair, h.x <= l.x OR h.y <= l.y.
            # Staircase formulation: assign each pair to a coord. If all heavies below staircase in y
            # and all lights above staircase in y, then every pair with h.y <= l.y is satisfied, done.
            # If a heavy is to the LEFT of the staircase (small x), then it may still work via x-coord.
            #
            # Simpler: use y-coord constraint for all pairs. Then: all H.y <= all L.y that are "on the pair side".
            #
            # Nested interpretation: want all heavies below some threshold T, all lights above T.
            # Min cost = find T minimizing sum of (H above T) + (L below T) in y-coord.
            # This is 1D isotonic L1 - well, 1D sort problem.
            # In 2D with mixed coord use, min over T_y and T_x: not quite nested.
            pass
        return total

    # Simpler: compute 1D "all y" solution (all pairs use coord 1).
    aLy = np.log(L[:, 1])
    aHy = np.log(H[:, 1])
    # Need: all H.y <= all L.y. So threshold T such that H all below T, L all above T.
    # Cost = sum over H of max(0, H.y - T) + sum over L of max(0, T - L.y).
    # Min over T: convex piecewise linear - min is at the median.
    ys_sorted = sorted(aHy.tolist() + aLy.tolist())
    best_T_cost = float('inf')
    for T in ys_sorted + [ys_sorted[0] - 1, ys_sorted[-1] + 1]:
        c = sum(max(0, hy - T) for hy in aHy) + sum(max(0, T - ly) for ly in aLy)
        if c < best_T_cost: best_T_cost = c
    # Also check mixed: some pairs use coord 0, others use coord 1.
    # For 2-level, pair-cover-free: there's a known SPAT algorithm?
    return best_T_cost


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 42
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    rng = random.Random(seed)
    for k in range(N):
        nH = rng.randint(1, 3)
        nL = rng.randint(1, 3)
        H = np.array([[rng.randint(1, 10), rng.randint(1, 10)] for _ in range(nH)], float)
        L = np.array([[rng.randint(1, 10), rng.randint(1, 10)] for _ in range(nL)], float)
        bf = anti_dom_2_brute(H, L)
        st = anti_dom_2_staircase_dp(H, L)
        tag = " TIGHT" if abs(bf - st) < 1e-6 else " GAP"
        print(f"nH={nH} nL={nL} brute={bf:.4f} y-only-threshold={st:.4f}{tag}", flush=True)
