import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, itertools
from ws_gap import solve
from core import weakly_solvable
d=np.load("cprime_yfound.npz"); Qs=d['Qs']; Y=d['Y']
for sub in [(0,),(1,),(2,),(3,),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]:
    r=solve([Qs[i] for i in sub],Y)
    if r is None: print(sub,"infeasible"); continue
    levels,z,t=r; lev=[levels.index(round(v,9)) for v in Y]; y=np.array([z[l] for l in lev])
    print(sub,"gap/range %.4f"%(t/1e-3),"weak at 4:",[weakly_solvable(Q,y) for Q in Qs],flush=True)
