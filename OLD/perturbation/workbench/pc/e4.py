import numpy as np, sys
sys.path.insert(0,'pc')
from land import lp_cost
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
G=np.linspace(0.02,0.98,25)
found=0
for trial in range(300):
    nl=rng.integers(3,7)
    # lights near a convex anti-diagonal-ish chain, heavy inside
    xs=np.sort(rng.uniform(0.5,6,nl)); ys=np.sort(rng.uniform(0.5,6,nl))[::-1]
    L=np.c_[xs,ys]
    h=np.array([rng.uniform(xs.min(),xs.max()), rng.uniform(ys.min(),ys.max())])
    P=np.vstack([L,h]); hi=nl
    c=np.array([lp_cost(P,[hi],list(range(nl)),{hi:g}) for g in G])
    mins=[i for i in range(len(G)) if (i==0 or c[i]<=c[i-1]-1e-7) and (i==len(G)-1 or c[i]<c[i+1]-1e-7)]
    # strict local minima after smoothing
    lm=[i for i in range(1,len(G)-1) if c[i]<c[i-1]-1e-6 and c[i]<=c[i+1]+1e-9]
    if len(lm)>=2 and np.isfinite(c).all():
        found+=1
        print("trial",trial,"nl",nl,"local minima at lam",[round(G[i],2) for i in lm],"vals",[round(c[i],4) for i in lm]); print(np.round(P,2).tolist())
print("found",found)
