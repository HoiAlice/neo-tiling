"""A: one max-min-gap LP against ALL vertex-bit patterns; then flow-LP check per pattern for a range of eps."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_gap import solve
from core import weakly_solvable
f=sys.argv[1]; d=np.load(f); Qs=list(d['Qs']); Y=d['Y']; pats=d['pats']; cost=d['cost']
print("patterns",len(Qs),"costs",np.round(cost-cost.min(),4).tolist(),flush=True)
r=solve(Qs,Y)
if r is None: print("JOINT INFEASIBLE for all patterns")
else:
    levels,z,t=r; lev=[levels.index(round(v,9)) for v in Y]
    eta=np.array([(z[l]-z.min())/(z.max()-z.min()) for l in lev]); print("feasible; min gap/range",t/1e-3)
    np.save(f.replace(".npz","_eta.npy"),eta)
    for eps in [1e-3,1e-2,0.1,0.3,0.6]:
        y=1+eps*eta; print(" eps",eps,[bool(weakly_solvable(Q,y)) for Q in Qs],flush=True)
# which patterns can be dropped: per-pattern feasibility
per=[solve([Q],Y) is not None for Q in Qs]; print("per-pattern feasible",per)
if r is None:
    # minimal infeasible set of patterns (deletion filter)
    keep=list(range(len(Qs)))
    for i in range(len(Qs)):
        tr=[j for j in keep if j!=i]
        if tr and solve([Qs[j] for j in tr],Y) is None: keep=tr
    print("minimal infeasible pattern set",[pats[j].tolist() for j in keep])
