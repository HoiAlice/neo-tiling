import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_rule import *
from ws_p9 import minimal_switches
from core import weakly_solvable
def nm(q): return "s%d%s"%(q//2,"t" if q%2==0 else "b")
sw=build("cp"); d=np.load("ws_snap_cp.npz"); pats=d['pats'].tolist(); Qs=list(d['Qs'])
Q=Qs[pats.index([0,1,0,1])]
for c in (0.02,):
    y=y_rule(sw,c); print("c",c,"weak",weakly_solvable(Q,y))
    k,P=minimal_switches(Q,y); print("min switches",k)
    for p in P: print(" ",nm(p),"s_c",int(sc(sw)[p//2]),tuple(np.round(Q[p],4)),"y %.4f"%y[p])
