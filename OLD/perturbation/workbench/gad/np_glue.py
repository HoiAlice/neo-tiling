"""np_glue.py -- interface agreement for K^+: glue the optimum of the crossing core K with isolated-optimum neighbours and test ALL conflicts of K^+
(non-strict, slack = max_c (x_b,c - x_a,c) for conflict (a higher y, b lower)); min slack > 0 proves S_{K+} = S_K + sum B(neighbours) (lower bound by relaxation)."""
import itertools, math
import numpy as np
from np_dual import *
from np_cross import crossing
from np_kplus import kplus
for pat in [(0, 1, 0, 0), (1, 0, 0, 0)]:
    swK = crossing(); bK = Block(swK)
    fixed = {bK.own[i]: b for i, b in zip((0, 3, 4, 8), pat)}
    lo, hi, asg, st = branch_and_bound(bK, fixed, tol=1e-9)
    val, lam, xK = dual_float(bK, asg)
    # bits of K switches from the routing of own pairs
    bitsK = [asg[bK.own[i]] for i in range(9)]
    swP = kplus(); bP = Block(swP)       # idx 0..5 U (1..4 = K U), 6..12 V (7..11 = K V)
    mapK = {0: 1, 1: 2, 2: 3, 3: 4, 4: 7, 5: 8, 6: 9, 7: 10, 8: 11}   # K index -> K+ index
    x = np.zeros((bP.T, 2)); bits = [None] * 13
    for k, kp in mapK.items():
        x[2 * kp] = xK[2 * k]; x[2 * kp + 1] = xK[2 * k + 1]; bits[kp] = bitsK[k]
    # neighbours: U0 (index 0) relation ne with U1 ; U5 ne with U4 ; V6 eq V7 ; V12 eq V11
    bits[0] = 1 - bits[1]; bits[5] = 1 - bits[4]; bits[6] = bits[7]; bits[12] = bits[11]
    for kp in (0, 5, 6, 12):
        d = swP[kp][2]; dl = d * H; s = bits[kp]
        x[2 * kp] = bP.A[2 * kp]; x[2 * kp + 1] = bP.A[2 * kp + 1]
        x[2 * kp][s] -= dl / 2; x[2 * kp + 1][s] += dl / 2
    sl = []
    for (a, b) in bP.conf:
        s = max(x[b][0] - x[a][0], x[b][1] - x[a][1]); sl.append((s, a, b))
    sl.sort()
    nb = {0, 1, 10, 11, 12, 13, 14, 15, 24, 25, 12 * 2, 12 * 2 + 1, 0, 1, 10, 11}
    nbpts = {0, 1, 10, 11, 12, 13, 24, 25}
    ownp = {(2 * i, 2 * i + 1) for i in range(13)}
    cross = [t for t in sl if (t[1] not in nbpts and t[2] not in nbpts) is False and (t[1], t[2]) not in ownp]
    print("   neighbour-involving non-own conflicts: smallest slacks", [(round(t[0], 4), t[1], t[2]) for t in cross[:5]])
    nonown = [t for t in sl if (t[1], t[2]) not in ownp]
    print("   non-own conflicts overall: smallest slacks", [(round(t[0], 6), t[1], t[2]) for t in nonown[:4]])
    print("pattern", pat, "K bits", bitsK, "min slack over all K+ conflicts %.6f" % sl[0][0], "pair", sl[0][1:], "; min slack involving a neighbour point %.6f" % min(t[0] for t in cross))
    c = sum(math.exp(abs(x[t][c_] - bP.A[t][c_])) - 1 for t in range(bP.T) for c_ in range(2))
    SB = sum(B_closed(s[2]) for s in swP)
    print("  glued cost %.9f  = K opt %.9f + sum B(nbrs) %.9f" % (c, hi, sum(B_closed(swP[k][2]) for k in (0, 5, 6, 12))))
