import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, cx2, cprime, k3
from ws_p9g import snap
from ws_gap import solve
from core import weakly_solvable
res=np.load("ws_ser2.npy",allow_pickle=True)
def build(kind):
    sw,idx=(cprime.build_c() if kind=="cp" else k3.build()); A,Y,conf,ks=cx2.setup(sw); return A,Y
out={}
for kind in ("cp","k3"):
    A,Y=build(kind); Qs={}
    if kind=="cp":
        d=np.load("cprime_yfound.npz")
        for p,Q in zip([(0,1,0,1),(0,1,1,0),(1,0,0,1),(1,0,1,0)],d['Qs']): Qs[p]=np.exp(snap(np.log(Q),1e-5))
        s=np.load("ws_ser.npz")
        for p,sg,Q in zip(s['pats'].tolist(),s['sigma'],s['Qs']):
            from core import polish_margin
            import cx2 as c2
            sw,idx=cprime.build_c(); A_,Y_,conf,ks=c2.setup(sw)
            cm,u=polish_margin(A_,conf,[int(v) for v in sg],1e-8); Qs[tuple(p)]=np.exp(snap(u,1e-5))
    else:
        d=np.load("ws_k3.npz")
        for p,Q in zip([(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0)],d['Qs']): Qs[p]=np.exp(snap(np.log(Q),1e-5))
    for r in res:
        if r[0]==kind: Qs[tuple(r[1])]=np.exp(snap(r[4],1e-5)); print(kind,r[1],"cost",round(r[3],5),flush=True)
    pats=sorted(Qs); print(kind,"patterns",len(pats))
    np.savez("ws_snap_%s.npz"%kind,Qs=np.array([Qs[p] for p in pats]),pats=np.array(pats),A=A,Y=Y)
