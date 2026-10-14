import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from core import weakly_solvable
eta=np.load("ws_eta_cprime.npz")['eta']; Y=np.load("ws_eta_cprime.npz")['Y']
d=np.load("ws_all_cp.npz"); pats=[tuple(p) for p in d['pats'].tolist()]
y=1+0.1*eta
def minimal_switches(Q,y):
    n=len(y)//2; keep=list(range(n))
    pts=lambda ks:[2*k+c for k in ks for c in (0,1)]
    assert not weakly_solvable(Q[pts(keep)],y[pts(keep)])
    for i in range(n):
        tr=[j for j in keep if j!=i]
        if not weakly_solvable(Q[pts(tr)],y[pts(tr)]): keep=tr
    # then points
    P=pts(keep)
    for q in list(P):
        tr=[p for p in P if p!=q]
        if not weakly_solvable(Q[tr],y[tr]): P=tr
    return keep,P
if __name__=="__main__":
  for pat in [(1,0,1,1),(0,0,1,1)]:
      Q=d['Qs'][pats.index(pat)]
      print(pat,"weak at y:",weakly_solvable(Q,y))
      k,P=minimal_switches(Q,y); print("  min switches",k,"points",[("s%d%s"%(p//2,"t" if p%2==0 else "b"),tuple(np.round(Q[p],4)),round(float(y[p]),5)) for p in P],flush=True)
