"""glue_u.py -- glued-point feasibility (Lemma G / rule R) for the retuned library: crossing core + wires, weak kink, stars.
usage: glue_u.py NAME p h u att aw"""
import sys, os, math, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import numpy as np
import phi_dual as pd
import lib_u as L
def kopt(u, pat):
    blk = pd.Block(L.crossing(u)); fixed = {blk.own[i]: b for i, b in zip((0, 3, 4, 8), pat)}
    lo, hi, asg, st = pd.branch_and_bound(blk, fixed, tol=1e-10)
    val, lam, x = pd.dual_float(blk, asg)
    return x, [asg[blk.own[i]] for i in range(9)], hi
def glue(sw, bits, cores=(), kinks=()):
    blk = pd.Block(sw); h = pd.H; x = blk.A.copy(); incore = set(); ptsK = set()
    for idx, pat, u in cores:
        xK, bK, _ = kopt(u, pat)
        for k, s in enumerate(idx):
            x[2*s] = xK[2*k]; x[2*s+1] = xK[2*k+1]; bits[s] = bK[k]; incore.add(s); ptsK |= {2*s, 2*s+1}
    for s in range(len(sw)):
        if s in incore: continue
        dl = sw[s][2] * h; b = bits[s]; x[2*s][b] -= dl/2; x[2*s+1][b] += dl/2
    for (i, j) in kinks:          # pooled weak pair: other coordinate c = 1 - bit, conflict (t_?, b_?) gap split
        c = 1 - bits[i]
        for a_, b_ in [(2*i, 2*j+1), (2*j, 2*i+1)]:
            d = x[a_][c] - x[b_][c]
            if d > 0 and x[a_][1-c] > x[b_][1-c] + 1e-12:
                x[a_][c] -= d/2; x[b_][c] += d/2
    cost = float(np.sum(pd.PHI.f(x - blk.A)))
    kp = [set(ij) for ij in kinks]
    worst = (9, None); worstK = (9, None)
    ownp = {(2*i, 2*i+1) for i in range(len(sw))}
    for (a, b) in blk.conf:
        if (a, b) in ownp or (a in ptsK and b in ptsK): continue
        sl = max(x[b][0]-x[a][0], x[b][1]-x[a][1])
        if any({a//2, b//2} == q for q in kp):
            worstK = min(worstK, (sl, (a, b))); continue
        worst = min(worst, (sl, (a, b)))
    return cost, worst, worstK, float(np.max(np.abs(x - blk.A))), blk
def xwires(u, mU, mV, pat):
    sw = []; Ui = []; Vi = []
    ts = [(-1.5*u - u*i) for i in range(mU, 0, -1)] + [(j - 1.5) * u for j in range(4)] + [1.5*u + u*i for i in range(1, mU+1)]
    for t in ts: Ui.append(len(sw)); sw.append((t, -t, 4, 1 + L.G, 1.0))
    for s in range(-2-mV, 3+mV):
        tp, bt = L.vlev(s); Vi.append(len(sw)); sw.append((s-0.5, s-0.5, 5, tp, bt))
    bits = [None]*len(sw)
    for k, i in enumerate(Ui): bits[i] = (pat[0] + k - mU) % 2
    for i in Vi: bits[i] = pat[2]
    idx = Ui[mU:mU+4] + Vi[mV:mV+5]
    return sw, bits, idx
if __name__ == '__main__':
    name = sys.argv[1]; p = None if sys.argv[2] == '-' else float(sys.argv[2]); h = float(sys.argv[3]); u = float(sys.argv[4]); att = float(sys.argv[5]); aw = float(sys.argv[6])
    pd.set_phi(name, h=h, p=p)
    SBf = lambda sw: sum(pd.B_closed(s[2]) for s in sw)
    XK = None
    print("== crossing core + wires (all conflicts, glued point)")
    for (mU, mV) in [(1, 1), (3, 3), (5, 5), (8, 8)]:
        for pat in [(0,1,0,0),(1,0,0,0),(0,1,1,1),(1,0,1,1)]:
            sw, bits, idx = xwires(u, mU, mV, pat)
            cost, worst, wk, D, blk = glue(sw, bits, [(idx, pat, u)], [])
            if XK is None: XK = kopt(u, pat)[2] - SBf(L.crossing(u))
            print("m=(%d,%d) %s cost-(sumB+X_K)=%.2e  min slack outside core %.4f h at %s  D=%.4f h" % (mU, mV, pat, cost - SBf(sw) - XK, worst[0]/h, worst[1], D/h), flush=True)
    print("== U wire with weak kink pooled (6 switches, weak in the middle), bits equal at kink")
    for steps in ([u, u, aw, u, u],):
        sw = L.uchain(steps); kink = (2, 3)
        for b0 in (0, 1):
            bits = [None]*6
            for i in range(6): bits[i] = (b0 + i) % 2 if i <= 2 else (b0 + i - 1) % 2   # equal bits at (2,3)
            cost, worst, wk, D, blk = glue(sw, bits, [], [kink])
            JE = 2*float(pd.PHI.f((4-aw)*h/2))
            print("steps", steps, "b0", b0, "cost-(sumB+J_e)=%.2e  min slack (non-kink) %.4f h ; kink-pair slack %.2e ; D %.4f h" % (cost - SBf(sw) - JE, worst[0]/h, wk[0], D/h))
    print("== stars with isolated optimum, all satisfied patterns")
    for arms in [('NW','SE','SW','NE'), ('NW','SE','SW'), ('NW','SW'), ('SE','NE')]:
        sw, rel = L.star(arms, u, att)
        n = len(sw); mins = 9; 
        for p_ in itertools.product((0, 1), repeat=n):
            if sum(c for (i, j, k, c) in rel if ((p_[i] == p_[j]) != (k == 'eq'))) == 0:
                cost, worst, wk, D, blk = glue(sw, list(p_), [], [])
                mins = min(mins, worst[0]/h)
        print(arms, "min slack over satisfied patterns %.4f h, cost-sumB=%.1e" % (mins, cost - SBf(sw)))
