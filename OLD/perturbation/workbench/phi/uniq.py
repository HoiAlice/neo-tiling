"""uniq.py -- r^2, K at u=2.5: are the optimal points of the satisfied patterns unique (over all routings), and is strict complementarity true
(tight conflicts have positive multipliers, others positive slack)?  Collect all leaves within 1e-7 of the best value."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import phi_dual as pd
import lib_u as L
pd.set_phi('sq', h=1.0)
def leaves(blk, fixed, tol=1e-7):
    out = []; best = [1e18]; stack = [(dict(fixed), None)]
    while stack:
        asg, lam0 = stack.pop()
        val, lam, x = pd.dual_float(blk, asg, lam0)
        if val > best[0] + tol: continue
        v = pd.violated(blk, asg, x, tol=1e-9)
        if v is None:
            cost = float(np.sum(pd.PHI.f(x - blk.A)))
            best[0] = min(best[0], cost); out.append((cost, x, dict(asg), lam)); continue
        for c in (0, 1):
            a2 = dict(asg); a2[v[1]] = c; stack.append((a2, lam))
    best = min(o[0] for o in out)
    return [o for o in out if o[0] < best + 1e-7]
for u in (2.5, 2.25):
    blk = pd.Block(L.crossing(u))
    for pat in [(0, 1, 0, 0), (0, 1, 1, 1)]:
        fixed = {blk.own[i]: b for i, b in zip((0, 3, 4, 8), pat)}
        ls = leaves(blk, fixed)
        xs = [o[1] for o in ls]
        spread = max(np.max(np.abs(x - xs[0])) for x in xs)
        cost, x, asg, lam = ls[0]
        tight = []; slack_non = 9
        for k, (a, b) in enumerate(blk.conf):
            c = asg.get(k)
            sl = [x[b][cc] - x[a][cc] for cc in (0, 1)]
            if c is not None and abs(sl[c]) < 1e-7: tight.append(lam.get(k, 0.0))
            elif c is not None: slack_non = min(slack_non, sl[c])
            else: slack_non = min(slack_non, max(sl))
        print("u", u, pat, "optimal leaves", len(ls), "max coordinate spread between them %.1e" % spread, "| tight conflicts", len(tight), "min multiplier %.4g" % min(tight), "| min slack of non-tight %.4g" % slack_non, "cost %.9f" % cost)
