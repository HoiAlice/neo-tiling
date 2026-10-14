import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, itertools
from ws_gap import solve
from core import weakly_solvable
d=np.load("ws_k3.npz"); Qs=d['Qs']; Y=d['Y']
for k in (1,2,3):
  for sub in itertools.combinations(range(6),k):
    r=solve([Qs[i] for i in sub],Y)
    if r is None: continue
    levels,z,t=r; lev=[levels.index(round(v,9)) for v in Y]; y=np.array([z[l] for l in lev])
    w=[weakly_solvable(Q,y) for Q in Qs]
    if all(w): print(sub,"suffices; gap/range %.4f"%(t/1e-3),flush=True)
  print("size",k,"done",flush=True)
