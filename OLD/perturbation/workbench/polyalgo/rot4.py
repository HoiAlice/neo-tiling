import numpy as np, sys, itertools
sys.path.insert(0,'.')
from rot3 import *
rng=np.random.default_rng(1); 
for it in range(60):
    T=int(rng.integers(4,9)); U=rng.normal(size=(T,2)); lev=rng.integers(1,3,size=T)
    if len(set(lev))<2: continue
    b=brute_L1(U,lev); r=best_interleave(U,lev)
    if abs(r-b)>1e-6 and T==7:
        allb=min(lp_inter(U,lev,list(o)) for o in itertools.permutations(range(T)))
        print("T=7 brute",b,"interleave",r,"all total orders",allb); break
