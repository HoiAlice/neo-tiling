"""C: window LPs. For each spatial window (switches with centre within radius r of a centre switch) solve the max-min-gap problem restricted to the window's points
(necessary condition for the full layout), against all patterns. Report per-window feasibility and relative gap; compare with the global one."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_gap import solve
f=sys.argv[1]; r=float(sys.argv[2]); d=np.load(f); Qs=list(d['Qs']); Y=d['Y']; A=d['A']
cen=(A[0::2]+A[1::2])/2; n=len(cen)
seen=set(); out=[]
for i in range(n):
    W=tuple(j for j in range(n) if np.abs(cen[j]-cen[i]).max()<=r)
    if W in seen or len(W)<3: continue
    seen.add(W); pts=[2*j+k for j in W for k in (0,1)]
    res=solve([Q[pts] for Q in Qs],Y[pts])
    out.append((W,None if res is None else res[2]/1e-3))
    print("window around",i,"size",len(W),"gap/range",None if res is None else round(res[2]/1e-3,4),flush=True)
print("min over windows",min((o[1] for o in out if o[1] is not None),default=None),"infeasible windows",[o[0] for o in out if o[1] is None])
