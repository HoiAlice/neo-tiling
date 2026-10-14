import numpy as np, sys
from exact import rho_exact
from pair import rho_pair
from gcons import g_construct, dom_ok
rng=np.random.default_rng(int(sys.argv[1]));N=int(sys.argv[2])
bad_closed=0;bad_g=0;bad_below=0
for it in range(N):
    T=int(rng.integers(3,13)); L=int(rng.integers(2,7)); G=int(rng.integers(3,14))
    a=rng.integers(0,G,(T,2)).astype(float); y=rng.integers(0,L,T).astype(float)
    rp=rho_pair(a,y)
    if rho_exact(a,y,False,rfix=rp) is None: bad_closed+=1; print("closed infeasible at pair bound",a.tolist(),y.tolist())
    if rp>0 and rho_exact(a,y,False,rfix=rp-1e-3) is not None: bad_below+=1
    u=g_construct(a,y,rp+1e-4)
    if u is None or not dom_ok(u,y): bad_g+=1
print("N",N,"closed-infeasible",bad_closed,"feasible-below",bad_below,"g-fail",bad_g)
