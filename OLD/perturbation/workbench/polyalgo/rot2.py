import numpy as np, sys
sys.path.insert(0,'.')
from rot import *
rng=np.random.default_rng(3);best=None
for it in range(3000):
    T=int(rng.integers(3,5)); U=rng.integers(0,5,size=(T,2)).astype(float); lev=rng.integers(1,3,size=T)
    if len(set(lev))<2: continue
    b=brute_L1(U,lev); r=rot_lp(U,lev)
    if r>b+1e-7 and (best is None or T<best[0]): best=(T,U.tolist(),lev.tolist(),b,r)
print(best)
