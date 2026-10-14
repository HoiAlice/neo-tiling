"""tight.py -- for the satisfied pattern (0,1,0,0) of K: routing + tight-conflict set of the optimum, per phi (is the order/tie structure phi-independent?)"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import phi_dual as pd
sys.modules['np_dual'] = pd
sys.path.insert(0, '/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad')
from np_cross import crossing
res = {}
for name, p, h in [('pi', None, 0.1951606566777282), ('pi', None, 0.5), ('sq', None, 0.2), ('cosh', None, 0.2), ('pow', 1.5, 0.2), ('pow', 1.25, 0.2), ('pow', 3.0, 0.2)]:
    pd.set_phi(name, h=h, p=p)
    blk = pd.Block(crossing())
    fixed = {blk.own[i]: b for i, b in zip((0, 3, 4, 8), (0, 1, 0, 0))}
    lo, hi, asg, st = pd.branch_and_bound(blk, fixed, tol=1e-9)
    val, lam, x = pd.dual_float(blk, asg)
    tight = set()
    for k, (a, b) in enumerate(blk.conf):
        c = asg[k] if k in asg else None
        sl = [x[b][c_] - x[a][c_] for c_ in (0, 1)]
        if max(sl) < 1e-6: tight.add((k, 0 if sl[0] >= sl[1] else 1))
    moves = tuple(round(float(x[t][c] - blk.A[t][c]) / h, 3) for t in range(blk.T) for c in (0, 1))
    res[(pd.PHI.name, h)] = (tight, asg)
    print(pd.PHI.name, h, "cost %.6f" % hi, "|asg|", len(asg), "#tight", len(tight), flush=True)
ks = list(res)
base = res[ks[0]]
for k in ks[1:]:
    print(k, "tight set equals pi(h=.195)?", res[k][0] == base[0], " symmetric diff", len(res[k][0] ^ base[0]))
