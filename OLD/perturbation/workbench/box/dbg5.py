import numpy as np, itertools
from t_suf import resid
from lp_box import kappa_lp, lp_box
rng=np.random.default_rng(1)
T=int(rng.integers(3,5)); P=rng.uniform(0.5,4,(T,2)); y=np.round(rng.uniform(0,3,T),2)
print(T,P.tolist(),y.tolist())
k=kappa_lp(P,y);print("kappa*",k, "at 1:",lp_box(P,y,1.0))
print("resid at P:",resid(P,y))
for kap in [k*1.02,k*1.3,k*3]:
    lo=P/kap;hi=P*kap;best=9
    for corner in itertools.product([0,1],repeat=2*T):
        s=np.array(corner).reshape(T,2);best=min(best,resid(lo+s*(hi-lo),y))
    for _ in range(300):
        s=rng.uniform(0,1,(T,2));best=min(best,resid(lo+s*(hi-lo),y))
    print(kap,best,lp_box(P,y,kap))
