import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_gap import solve
from core import weakly_solvable
d=np.load("cprime_yfound.npz"); Qs=d['Qs']; Y=d['Y']; A=np.load("cprime_Q_1010.npz")['A']; P=np.exp(A)
for name,base in [("P only",[P]),("P+Q0",[P,Qs[0]]),("Q0 only",[Qs[0]])]:
    r=solve(base,Y)
    if r is None: print(name,"infeasible"); continue
    levels,z,t=r; lev=[levels.index(round(v,9)) for v in Y]; y=np.array([z[l] for l in lev])
    print(name,"gap/range",t/1e-3,"weak at 4 Q:",[weakly_solvable(Q,y) for Q in Qs],"at P",weakly_solvable(P,y))
