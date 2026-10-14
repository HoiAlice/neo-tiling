import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
import ws_two as W
from ws_p9 import minimal_switches
from core import weakly_solvable
y=W.y_multi(W.K,W.SL,0.3); i,j=W.pats.index([0,1,0,1]),W.pats.index([0,1,0,1])
Q=W.Qcat(i,j); print("weak",weakly_solvable(Q,y))
# which pattern pairs pass?
ok=[(a,b) for a,b in [(i,j),(i,W.pats.index([1,0,1,0])),(W.pats.index([1,0,1,0]),i)] ]
k,P=minimal_switches(Q,y); print("min switches",k)
s=W.s
for p in P: print(" ","c%d s%d%s"%(p//(2*W.n1),(p%(2*W.n1))//2,"t" if p%2==0 else "b"),"s_c",int(s[p//2]),tuple(np.round(Q[p],3)),"y %.4f"%y[p])
