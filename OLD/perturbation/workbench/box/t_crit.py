import numpy as np, sys
from crit import critical_kappas
from lp_box import kappa_lp
seed=int(sys.argv[1]);N=int(sys.argv[2]);bad=0;tot=0
for it in range(N):
    r=np.random.default_rng([seed,it]);T=int(r.integers(3,6));P=r.uniform(0.5,4,(T,2));y=np.round(r.uniform(0,3,T),2)
    k=kappa_lp(P,y,iters=50)
    if k==1.0: continue
    tot+=1; cr=np.array(critical_kappas(P)); d=np.abs(cr-k).min()
    if d>1e-7: bad+=1; print("NOT critical",it,k,d)
print("tested",tot,"not-in-critical-set",bad,"; |crit|~",len(cr))
