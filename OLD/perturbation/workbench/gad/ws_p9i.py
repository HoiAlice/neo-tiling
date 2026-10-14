import sys; sys.path.insert(0,".")
from ws_p9b import *
from ws_gap import solve
from ws_p9g import snap
from core import polish_margin
d=np.load("ws_ser.npz"); conf_l=[tuple(c) for c in d['conf'].tolist()]
for i,p in enumerate(d['pats'].tolist()):
    cm,u=polish_margin(A,conf_l,[int(s) for s in d['sigma'][i]],1e-8); Q=np.exp(snap(u,1e-5))
    r=solve([Q],Y); print(tuple(p),"snapped: own-y t =",None if r is None else round(r[2]/1e-3,4),flush=True)
