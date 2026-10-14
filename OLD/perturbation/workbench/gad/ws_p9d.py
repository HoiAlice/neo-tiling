import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from core import weakly_solvable
from ws_gap import solve
d=np.load("ws_ser.npz"); eta=np.load("ws_eta_cprime.npz")['eta']
for eps in (1e-3,0.1):
    y=1+eps*eta
    print("eps",eps,{tuple(p):bool(weakly_solvable(Q,y)) for p,Q in zip(d['pats'].tolist(),d['Qs'])},flush=True)
Y=d['Y']
print("per-pattern strict t (own y):",{tuple(p):round(r[2]/1e-3,4) if (r:=solve([Q],Y)) else 0.0 for p,Q in zip(d['pats'].tolist(),d['Qs'])})
