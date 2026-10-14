import numpy as np, sys
sys.path.insert(0,'.')
from lib import *
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
for K in (2,3):
  bad=0;frac=0;n=0
  for it in range(40):
    T=int(rng.integers(4,8))
    U=rng.normal(size=(T,2)).round(2)*1.0
    lev=rng.integers(1,K+1,size=T)
    if len(set(lev))<K: continue
    b=brute_L1(U,lev); g,_=grid_model(U,lev); r,_=grid_model(U,lev,relax=True)
    n+=1; bad+= abs(b-g)>1e-6; frac+= abs(g-r)>1e-6
  print("K",K,"n",n,"grid-ILP != brute:",bad,"LP != ILP:",frac)
