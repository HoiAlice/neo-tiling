import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
import ws_two as W
from ws_rule import setup_with
y=W.y_multi(W.K,[0.02,0.07,0.12],0.3)
# all conflicting pairs (no distance filter), cross-copy only
Ab=np.vstack([np.load("ws_snap_cp.npz")['A']]*2)/0.2; Ab[2*W.n1:]+=np.array([W.DX,W.DY])
n=len(y); best=1e9; arg=None; cnt=0
for a in range(n):
    for b in range(n):
        if (a<2*W.n1)!=(b<2*W.n1) and y[a]>y[b]:
            sep=max(Ab[b,0]-Ab[a,0],Ab[b,1]-Ab[a,1])
            if sep<best: best,arg=sep,(a,b)
a,b=arg; nm=lambda q:"c%d s%d%s"%(q//(2*W.n1),(q%(2*W.n1))//2,"t" if q%2==0 else "b")
print("shift",W.DX,W.DY,"min separation over cross-copy conflict pairs (grid units): %.1f"%best,"at",nm(a),tuple(Ab[a]),"->",nm(b),tuple(Ab[b]))
