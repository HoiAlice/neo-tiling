import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_rule import *
from ws_rule4 import y_pw
from ws_p9 import minimal_switches
from core import weakly_solvable
sw=build("cp"); d=np.load("ws_snap_cp.npz"); Qs=list(d['Qs']); pats=d['pats'].tolist()
def nm(q): return "s%d%s"%(q//2,"t" if q%2==0 else "b")
y=y_pw(sw,0.02,0.063,4)
for pi in pats:
    Q=Qs[pats.index(pi)]
    if not weakly_solvable(Q,y):
        print(pi,'FAILS')
        k,P=minimal_switches(Q,y); print(" points:")
        for p in P: print("  ",nm(p),"s_c",int(sc(sw)[p//2]),tuple(np.round(Q[p],4)),"y %.4f"%y[p])
        break
