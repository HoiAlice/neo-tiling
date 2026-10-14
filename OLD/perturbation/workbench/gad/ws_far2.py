import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
import ws_two as W
from ws_far import farkas
from ws_p9 import minimal_switches
from core import weakly_solvable
gap=float(os.environ.get("WS_GAP","0.0005"))
y=W.y_multi(W.K,W.SL,0.3,gap=gap)
Ab=np.vstack([np.load("ws_snap_cp.npz")['A']]*2)/0.2; Ab[2*W.n1:]+=W.D
for pi in [[0,1,0,1],[1,0,1,0],[0,0,0,0],[1,1,1,1]]:
    k=W.pats.index(pi); Q=W.Qcat(k,k)
    if weakly_solvable(Q,y): print(pi,"ok"); continue
    kk,P=minimal_switches(Q,y); lam,val,nf=farkas(Q[P],y[P]); print(pi,"FAIL; points",len(P),"min lam.y",val)
    for a,p in zip(lam,P):
        if abs(a)>1e-6:
            sw_i=p//2; print("  lam %+.3f"%a,"c%d s%d%s"%(p//(2*W.n1),sw_i%W.n1,"t" if p%2==0 else "b"),"(x,y)=(%.1f,%.1f) s=%.1f t=%.1f"%(Ab[p,0],Ab[p,1],Ab[p].sum(),Ab[p,1]-Ab[p,0]),"s_c",int(W.s[sw_i]),"y %.5f"%y[p])
    break
