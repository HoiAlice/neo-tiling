import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_B2 import rule
from core import weakly_solvable
d=np.load("ws_snap_k3.npz"); Qs=list(d['Qs']); A=d['A']; Y=d['Y']
for how in ("meanp","minp"):
    good=[]
    for c,m in [(0.1,0.01),(0.3,0.01),(0.3,0.03),(1,0.01),(1,0.03),(1,0.1),(3,0.03),(3,0.1)]:
        e=rule(Y,A,c,m,how); ok=[weakly_solvable(Q,1+0.1*x) for Q in Qs for x in [e]]
        if all(ok): good.append((c,m))
        else: print(how,c,m,"fails",[tuple(p) for p,o in zip(d['pats'].tolist(),ok) if not o],flush=True)
    print("K3 all 8:",how,"passing",good,flush=True)
