"""Experiment 1: is the designed y in the axis-parallel sub-cone at the 16 snapped cprime optima?"""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"../gad"); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from axcone import cone_lp, check_decomp, AX
from ws_rule import build
from ws_rule4 import y_pw
from core import weakly_solvable
sw=build("cp"); d=np.load("../gad/ws_snap_cp.npz"); Qs=list(d['Qs']); pats=d['pats'].tolist()
D3=AX+[(1.0,1.0)]
for (c1,c2,ss,gap) in [(0.02,0.07,4,0.01),(0.02,0.12,4,0.002),(0.02,0.62,4,0.002)]:
    y=y_pw(sw,c1,c2,ss,gap=gap)
    for p,Q in zip(pats,Qs):
        full=bool(weakly_solvable(Q,y))
        okA,infoA=cone_lp(Q,y,AX,margin=True)
        ok3,info3=cone_lp(Q,y,D3,margin=True)
        print((c1,c2,ss,gap),p,"full",full,"| axis-cone",okA,"t=%.2e"%infoA['t'],"| +diag",ok3,"t=%.2e"%info3['t'],flush=True)
