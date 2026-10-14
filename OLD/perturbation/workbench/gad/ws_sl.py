import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_rule import *
from ws_rule4 import y_pw
from core import weakly_solvable
sw=build("cp"); d=np.load("ws_snap_cp.npz"); Qs=list(d['Qs'])
for c1,c2 in [(0.02,0.07),(0.07,0.12),(0.07,0.14),(0.07,0.17),(0.12,0.17),(0.12,0.24),(0.05,0.1)]:
    y=y_pw(sw,c1,c2,4); ok=[weakly_solvable(Q,y) for Q in Qs[::3]]
    print("single copy slopes",c1,c2,"fails",len(ok)-sum(ok),"of",len(ok),flush=True)
