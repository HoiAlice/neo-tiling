"""np_cluster.py -- glued-point feasibility for whole clusters (item 2).  Build Q* from: crossing cores at their B&B optimum, all other switches at the isolated
optimum, weak kinks pooled; test ALL conflicts (full set) and report min slack outside the cores, cost vs closed form, and displacement bound D."""
import re, sys, itertools, math
import numpy as np
from np_dual import *
from np_cross import crossing
KSW = crossing(); KBLK = Block(KSW)
_cache = {}
def core_opt(pat):
    if pat not in _cache:
        fixed = {KBLK.own[i]: b for i, b in zip((0, 3, 4, 8), pat)}
        lo, hi, asg, st = branch_and_bound(KBLK, fixed, tol=1e-9)
        val, lam, x = dual_float(KBLK, asg)
        _cache[pat] = (x, [asg[KBLK.own[i]] for i in range(9)], hi)
    return _cache[pat]
def glue(sw, bits, cores, kinks):
    """cores: list of (list of 9 switch indices in K order, terminal pattern); kinks: list of (i,j) weak pairs with equal bits."""
    blk = Block(sw); x = blk.A.copy(); Dmax = 0.0
    incore = set()
    for idx, pat in cores:
        xK, bK, _ = core_opt(pat)
        for k, s in enumerate(idx):
            x[2*s] = xK[2*k]; x[2*s+1] = xK[2*k+1]; bits[s] = bK[k]; incore.add(s)
    for s in range(len(sw)):
        if s in incore: continue
        dl = sw[s][2] * H; b = bits[s]
        x[2*s][b] -= dl/2; x[2*s+1][b] += dl/2
    for (i, j) in kinks:
        c = 1 - bits[i]
        for a_, b_ in [(2*i, 2*j+1), (2*j, 2*i+1)]:
            if (a_, b_) in blk.cidx:
                d = x[a_][c] - x[b_][c]
                if d > 0 and min(x[a_][1-c]-x[b_][1-c], 1) > 0 or d > 0:
                    if x[a_][1-c] > x[b_][1-c] + 1e-12:
                        x[a_][c] -= d/2; x[b_][c] += d/2
    cost = sum(math.exp(abs(x[t][c]-blk.A[t][c])) - 1 for t in range(blk.T) for c in range(2))
    ownp = {(2*i, 2*i+1) for i in range(len(sw))}
    ptsK = {p for idx, _ in cores for s in idx for p in (2*s, 2*s+1)}
    worst = (9, None); worstK = (9, None)
    kp = {s for ij in kinks for s in ij}
    for (a, b) in blk.conf:
        sl = max(x[b][0]-x[a][0], x[b][1]-x[a][1])
        if (a, b) in ownp: continue
        if a in ptsK and b in ptsK: continue
        if (a//2 in kp and b//2 in kp and any(a//2 in ij and b//2 in ij for ij in kinks)):
            if sl < worstK[0]: worstK = (sl, (a, b))
            continue
        if sl < worst[0]: worst = (sl, (a, b))
    D = np.max(np.abs(x - blk.A))
    return cost, worst, D, x, blk, worstK
