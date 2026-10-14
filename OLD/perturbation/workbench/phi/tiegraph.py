"""tiegraph.py -- r^2, K at G* (u=2.5), 4 satisfied patterns: routed tight constraints with positive multiplier -> equality components per coordinate;
are all coordinate coincidences x_a = x_b of the optimum (within K, and K points vs the iso-neighbour positions) implied by these components?
also min slack of non-tight conflicts and the pseudo-inverse norm kappa of the active constraint matrix."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import phi_dual as pd, lib_u as L
pd.set_phi('sq', h=1.0)
u = 2.5
blk = pd.Block(L.crossing(u)); T = blk.T
for pat in [(0, 1, 0, 0), (1, 0, 0, 0), (0, 1, 1, 1), (1, 0, 1, 1)]:
    fixed = {blk.own[i]: b for i, b in zip((0, 3, 4, 8), pat)}
    lo, hi, asg, st = pd.branch_and_bound(blk, fixed, tol=1e-11)
    val, lam, x = pd.dual_float(blk, asg)
    parent = {c: list(range(T)) for c in (0, 1)}
    def find(c, i):
        while parent[c][i] != i: parent[c][i] = parent[c][parent[c][i]]; i = parent[c][i]
        return i
    act = []
    for k, c in asg.items():
        a, b = blk.conf[k]
        if lam.get(k, 0) > 1e-6:
            act.append((k, a, b, c)); ra, rb = find(c, a), find(c, b); parent[c][ra] = rb
    # coincidences
    unforced = []; ties = 0
    for c in (0, 1):
        for i in range(T):
            for j in range(i + 1, T):
                if abs(x[i][c] - x[j][c]) < 1e-6:
                    ties += 1
                    if find(c, i) != find(c, j): unforced.append((c, i, j))
    # non-tight conflict slack: best coordinate not equality-forced
    minsl = 9
    for k, (a, b) in enumerate(blk.conf):
        if (a, b) in {(2*i, 2*i+1) for i in range(9)}: pass
        sl = max(x[b][0] - x[a][0], x[b][1] - x[a][1])
        if sl > 1e-6: minsl = min(minsl, sl)
    # constraint matrix of active (multiplier>0) constraints on the 2T coordinates; kappa = 1/smallest singular value of the (n_act x 2T) matrix
    M = np.zeros((len(act), 2 * T))
    for r, (k, a, b, c) in enumerate(act): M[r, 2 * b + c] = 1; M[r, 2 * a + c] = -1
    sv = np.linalg.svd(M, compute_uv=False)
    print(pat, "active(+mult) %d, coincidences %d, not implied by active components: %s ; min positive slack of conflicts %.4f ; rank %d/%d, min sing. value %.3f" % (len(act), ties, unforced, minsl, np.sum(sv > 1e-9), len(act), sv[np.sum(sv > 1e-9) - 1]), flush=True)
