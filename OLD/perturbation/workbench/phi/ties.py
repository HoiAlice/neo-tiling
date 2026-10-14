import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import phi_dual as pd
import lib_u as L
u = 2.5
res = {}
for name, p, h in [('sq', None, 1.0), ('cosh', None, 0.05), ('cosh', None, 0.2), ('cosh', None, 0.4), ('cosh', None, 1.0)]:
    pd.set_phi(name, h=h, p=p)
    blk = pd.Block(L.crossing(u))
    pat = (0, 1, 0, 0)
    fixed = {blk.own[i]: b for i, b in zip((0, 3, 4, 8), pat)}
    lo, hi, asg, st = pd.branch_and_bound(blk, fixed, tol=1e-11)
    val, lam, x = pd.dual_float(blk, asg)
    tie = set(); 
    for k, (a, b) in enumerate(blk.conf):
        sl = [x[b][c] - x[a][c] for c in (0, 1)]
        for c in (0, 1):
            if abs(sl[c]) < 1e-6 * max(1, h) : tie.add((k, c))
    unr = [k for k in range(len(blk.conf)) if k not in asg and any(abs(x[blk.conf[k][1]][c] - x[blk.conf[k][0]][c]) < 1e-6 for c in (0, 1))]
    res[(name, h)] = tie
    print(name, h, "cost %.7f" % (hi / (h * h) if name == 'sq' else hi), "#ties", len(tie), "ties among unassigned conflicts:", [(blk.conf[k]) for k in unr], "max negative slack of any conflict %.1e" % min(max(x[b][0]-x[a][0], x[b][1]-x[a][1]) for a, b in blk.conf))
base = res[('sq', 1.0)]
for k, v in res.items(): print(k, "tie set equals r^2 tie set:", v == base, "sym diff", len(v ^ base))
