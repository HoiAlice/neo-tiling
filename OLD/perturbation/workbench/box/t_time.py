import numpy as np, time
from lp_box import lp_box, kappa_lp
for T in (5,10,15,20):
    r=np.random.default_rng(T);P=r.uniform(0.5,4,(T,2));y=np.round(r.uniform(0,3,T),2)
    t0=time.time();ok=lp_box(P,y,1.3)[0];t1=time.time()-t0
    t0=time.time();k=kappa_lp(P,y,iters=30);t2=time.time()-t0
    print(T,"one LP %.2fs"%t1,"kappa*=%.4f"%k,"bisection %.1fs"%t2,flush=True)
