import numpy as np, sys
from exact import rho_exact
from twosat import rho_2sat
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
bad=0;N=300
for it in range(N):
    T=int(rng.integers(4,11)); L=int(rng.integers(2,6)); G=int(rng.integers(4,12))
    a=rng.integers(0,G,(T,2)).astype(float); y=rng.integers(0,L,T).astype(float)
    r1=rho_exact(a,y); r2=rho_2sat(a,y)
    if abs(r1-r2)>1e-6:
        bad+=1; print("DIFF",T,L,r1,r2); 
        if bad<4: print(a.tolist(),y.tolist())
print("bad",bad,"of",N)
