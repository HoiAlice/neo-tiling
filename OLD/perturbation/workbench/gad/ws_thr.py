import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_rule import *
from ws_rule4 import y_pw
from ws_p9 import minimal_switches
from core import weakly_solvable
kind="cp"; sw=build(kind); d=np.load("ws_snap_cp.npz"); Qs=list(d['Qs']); pats=d['pats'].tolist()
def ok(c1,c2,idx=None):
    y=y_pw(sw,c1,c2,4); return all(weakly_solvable(Qs[i],y) for i in (range(len(Qs)) if idx is None else idx))
for c1 in (0.02,0.03):
    lo,hi=c1+0.001,0.2
    for _ in range(9):
        mid=(lo+hi)/2
        if ok(c1,mid): hi=mid
        else: lo=mid
    print("c1",c1,"threshold c2 ~",round(hi,4),"Delta",round(hi-c1,4),flush=True)
