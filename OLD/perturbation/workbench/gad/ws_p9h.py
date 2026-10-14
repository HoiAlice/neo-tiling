import sys; sys.path.insert(0,".")
from ws_p9b import *
from ws_p9 import minimal_switches
from core import polish_margin
d=np.load("ws_ser.npz"); conf_l=[tuple(c) for c in d['conf'].tolist()]
from ws_p9g import snap
i=1; cm,u=polish_margin(A,conf_l,[int(s) for s in d['sigma'][i]],1e-8); L=snap(u,1e-5); Q=np.exp(L)
np.save("ws_Q0011_snap.npy",Q)
print("weak",weakly_solvable(Q,y))
k,P=minimal_switches(Q,y); print("min switches",k)
for p in P: print(" ","s%d%s"%(p//2,"t" if p%2==0 else "b"),tuple(np.round(Q[p],6)),"y %.6f"%y[p])
