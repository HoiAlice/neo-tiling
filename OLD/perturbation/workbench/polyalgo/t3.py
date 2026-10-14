import numpy as np, sys
sys.path.insert(0,'.')
from lib import *
rng=np.random.default_rng(5); best=None
for it in range(150):
    T=int(rng.integers(3,6)); U=rng.integers(0,6,size=(T,2)).astype(float)
    lev=rng.integers(1,3,size=T)
    if len(set(lev))<2: continue
    g,_=grid_model(U,lev); r,_=grid_model(U,lev,relax=True)
    if g-r>1e-6 and (best is None or T<best[0]): best=(T,U.tolist(),lev.tolist(),g,r, brute_L1(U,lev))
print(best)
