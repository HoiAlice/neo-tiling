import numpy as np, sys
from boxdom import *
from exact import rho_exact
rng=np.random.default_rng(5); N=0; fails=0; milp_bad=0
def fam(kind,T,G):
    if kind=="rand": return rng.integers(0,G,(T,2)).astype(float)
    if kind=="anti":  # grid points on anti-diagonals
        s=rng.integers(0,G,T); return np.stack([s,G-1-s+rng.integers(0,2,T)],1).astype(float)
    if kind=="stair":  # nested staircases
        k=rng.integers(0,G,T); return np.stack([k+rng.integers(0,2,T),G-k+rng.integers(0,2,T)],1).astype(float)
    if kind=="diag": 
        s=rng.integers(0,G,T); return np.stack([s,s+rng.integers(-1,2,T)],1).astype(float)
    if kind=="real": return rng.uniform(0,G,(T,2))
cases=[]
for kind in ["rand","anti","stair","diag","real"]:
    for it in range(80):
        T=int(rng.integers(3,13));L=int(rng.integers(2,8));G=int(rng.integers(3,14))
        a=fam(kind,T,G); y=rng.integers(0,L,T).astype(float)
        cases.append((kind,a,y))
a=np.array([[4,1],[3,3],[1,4]],float);cases.append(("tri",a,np.array([1,5,3.])))
for kind,a,y in cases:
    N+=1; r=rho_dom(a,y)
    u=canonical(a,y,r)
    ok=dom_free(u,y) and np.abs(u-a).max()<=r+1e-9
    if not ok: fails+=1; print("CONSTR FAIL",kind,r)
    # MILP: feasible at r, infeasible below r
    if rho_exact(a,y,False,rfix=r) is None: milp_bad+=1; print("MILP infeasible at r",kind)
    if r>1e-6 and rho_exact(a,y,False,rfix=r-1e-4) is not None: milp_bad+=1; print("MILP feasible below",kind)
print("instances",N,"construction failures",fails,"MILP disagreements",milp_bad)
