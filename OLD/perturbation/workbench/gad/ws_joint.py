import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_gap import solve
from core import weakly_solvable
kind=sys.argv[1]; d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); Y=d['Y']; pats=d['pats']
r=solve(Qs,Y); print(kind,"joint over",len(Qs),"patterns:", None if r is None else "t=%.4f"%(r[2]/1e-3),flush=True)
if r and r[2]/1e-3>1e-6:
    levels,z,t=r; lev=[levels.index(round(v,9)) for v in Y]; eta=np.array([(z[l]-z.min())/(z.max()-z.min()) for l in lev])
    np.save("ws_eta16_%s.npy"%kind,eta)
    for eps in (0.01,0.1,0.3,0.6):
        ok=[bool(weakly_solvable(Q,1+eps*eta)) for Q in Qs]; print(" eps",eps,"all" if all(ok) else [tuple(p) for p,o in zip(pats.tolist(),ok) if not o],flush=True)
else:
    per=[(tuple(p),round((solve([Q],Y) or (0,0,0))[2]/1e-3,4)) for p,Q in zip(pats.tolist(),Qs)]; print("per pattern t",per)
    keep=list(range(len(Qs)))
    def tv(S):
        rr=solve([Qs[i] for i in S],Y); return 0 if rr is None else rr[2]/1e-3
    for i in range(len(Qs)):
        tr=[j for j in keep if j!=i]
        if tr and tv(tr)<1e-6: keep=tr
    print("minimal infeasible set",[tuple(pats[j]) for j in keep])
