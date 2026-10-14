import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
import ws_two as W
from ws_gap import solve
Y=W.y_multi(W.K,[0.02,0.07,0.12],0.3)
Ab=np.vstack([np.load("ws_snap_cp.npz")['A']]*2)/0.2; Ab[2*W.n1:]+=W.D
ij=(3,12)   # infeasible at D=10 in ws_free
Q=W.Qcat(*ij)
def feas(sws):
    pts=[2*k+c for k in sws for c in (0,1)]; r=solve([Q[pts]],Y[pts]); return r is not None and r[2]/1e-3>1e-6
sws=list(range(2*W.n1)); print("D",W.D,"pattern",W.pats[ij[0]],W.pats[ij[1]],"free-y feasible:",feas(sws),flush=True)
if not feas(sws):
    for i in list(sws):
        tr=[j for j in sws if j!=i]
        if not feas(tr): sws=tr
    print("minimal y-infeasible switches:",sws)
    for i in sws: print("  c%d s%d s_c=%d bottom=(%.1f,%.1f) d=%d"%(i//W.n1,i%W.n1,W.s[i],*(Ab[2*i+1]),round(Ab[2*i,0]-Ab[2*i+1,0])))
