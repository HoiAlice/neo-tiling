"""Max-min-gap eta (scale-free) -> y=1+eps*eta; test weak solvability at all optimal Q for several eps; compare with uniform-rank."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_gap import solve
from core import weakly_solvable
for f in ["cprime_yfound.npz","ws_k3.npz"]:
    d=np.load(f); Qs=list(d['Qs']); Y=d['Y']
    levels,z,t=solve(Qs,Y); lev=[levels.index(round(v,9)) for v in Y]
    eta=np.array([(z[l]-z.min())/(z.max()-z.min()) for l in lev])
    print(f,"min gap/range",t/1e-3,"eta distinct",len(set(np.round(eta,6))))
    for eps in [1e-3,1e-2,0.1,0.3,0.6,0.9]:
        y=1+eps*eta; print("  eps",eps,"ratio %.3f"%(y.max()/y.min()),all(weakly_solvable(Q,y) for Q in Qs),flush=True)
    np.savez("ws_eta_"+f.split(".")[0].replace("_yfound","")+".npz",eta=eta,Y=Y)
