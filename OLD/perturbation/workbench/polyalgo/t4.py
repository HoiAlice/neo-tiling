import numpy as np, sys, time
sys.path.insert(0,'.')
from lib import *
rng=np.random.default_rng(11)
for K in (2,3,4):
  n=bad=0;t0=time.time()
  for it in range(12):
    T=int(rng.integers(7,11)); U=rng.normal(size=(T,2))
    lev=rng.integers(1,K+1,size=T)
    if len(set(lev))<K: continue
    b=brute_L1(U,lev); g,_=grid_model(U,lev); n+=1; bad+=abs(b-g)>1e-6
  print("K",K,"n",n,"mismatch",bad,"time %.0fs"%(time.time()-t0),flush=True)
