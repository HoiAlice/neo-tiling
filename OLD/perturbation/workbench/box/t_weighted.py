import sys, numpy as np
from lp_box import lp_box
from construct import construct, resid_exact
seed=int(sys.argv[1]);N=int(sys.argv[2]);ok=tested=0
for it in range(N):
    r=np.random.default_rng([seed,it]);T=int(r.integers(3,6));P=r.uniform(0.5,4,(T,2));y=np.round(r.uniform(0,3,T),2);w=r.uniform(0.3,2,(T,2))
    K=lambda lam: np.exp(lam*w)
    if lp_box(P,y,K(0.0))[0]: continue
    lo,hi=0.0,1.0
    while not lp_box(P,y,K(hi))[0]: hi*=2
    for _ in range(40):
        m=(lo+hi)/2
        if lp_box(P,y,K(m))[0]: hi=m
        else: lo=m
    tested+=1;kap=K(hi*(1+1e-3));Q=construct(P,y,kap)
    if Q is None or isinstance(Q,tuple): print("FAIL",it,Q);continue
    inbox=(Q>=P/kap-1e-9).all() and (Q<=P*kap+1e-9).all();res=resid_exact(Q,y)
    ok+=inbox and res<1e-7
    # below: LP infeasible by construction of bisection; check random search quickly not needed
print("weighted full: constructed+verified",ok,"of",tested)
