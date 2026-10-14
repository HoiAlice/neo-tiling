import sys, itertools, numpy as np, time
sys.path.insert(0,'/Users/olegoleg/Code/neo-tiling/perturbation/experiments')
from iso_scipy import rho_dom_fast
rng=np.random.default_rng(int(sys.argv[1]))
sizes=eval(sys.argv[2]); n=int(sys.argv[3])
for it in range(n):
    T=sum(sizes)
    P=np.exp(rng.normal(0,0.5,(T,2)))
    y=np.concatenate([[k+1]*s for k,s in enumerate(sizes)]).astype(float)
    t0=time.time()
    full=rho_dom_fast(P,y)[0]
    lb=0
    L=len(sizes)
    for j in range(L-1):
        idx=[i for i in range(T) if y[i] in (j+1,j+2)]
        lb+=rho_dom_fast(P[idx],y[idx])[0]
    print(it,round(full,5),round(lb,5),"GAP" if full>lb+1e-6 else "", round(time.time()-t0,1),flush=True)
