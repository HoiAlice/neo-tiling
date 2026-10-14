import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_rule import *
from ws_rule4 import y_pw
from core import weakly_solvable
sw=build("cp"); d=np.load("ws_snap_cp.npz"); Qs=list(d['Qs']); pats=d['pats'].tolist()
res=[]
for p,Q in zip(pats,Qs):
    lo,hi=0.021,0.2
    for _ in range(8):
        mid=(lo+hi)/2
        if weakly_solvable(Q,y_pw(sw,0.02,mid,4)): hi=mid
        else: lo=mid
    res.append((round(hi-0.02,4),p)); print(p,"Delta_min",round(hi-0.02,4),flush=True)
