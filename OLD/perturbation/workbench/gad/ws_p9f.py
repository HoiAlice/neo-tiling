import sys; sys.path.insert(0,".")
from ws_p9b import *
from ws_p9 import minimal_switches
d=np.load("ws_ser.npz"); Q=np.round(d['Qs'][1],7)
print("pattern",d['pats'][1],"snapped weak:",weakly_solvable(Q,y))
k,P=minimal_switches(Q,y)
print("min switches",k)
for p in P: print(" ","s%d%s"%(p//2,"t" if p%2==0 else "b"),tuple(np.round(Q[p],6)),"y",round(float(y[p]),6),"Y",Y[p])
np.save("ws_p9f_pts.npy",np.array(P))
