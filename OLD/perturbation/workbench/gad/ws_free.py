import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
import ws_two as W
from ws_gap import solve
Y=W.y_multi(W.K,[0.02,0.07,0.12],0.3)
rng=np.random.default_rng(3); allp=[(i,j) for i in range(16) for j in range(16)]; sel=[allp[k] for k in rng.choice(256,4,replace=False)]
Qs=[W.Qcat(*ij) for ij in sel]
for k,Q in enumerate(Qs):
    r=solve([Q],Y); print("shift",W.DX,W.DY,"pattern",sel[k],"free-y single t:", 0 if r is None else round(r[2]/1e-3,5),flush=True)
r=solve(Qs,Y); print("shift",W.DX,W.DY,"joint over",len(Qs),"t:",0 if r is None else round(r[2]/1e-3,5),flush=True)
