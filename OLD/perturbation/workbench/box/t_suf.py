"""Sufficiency: at kappa = kappa*(1+eps) find Q in box with y weakly solvable (flow_lp residual 0) by local search; below kappa*(1-eps) none found."""
import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
from scipy.optimize import minimize
from lp_box import kappa_lp
def resid(Pq,y):
    Qf=[(Fraction(float(x)).limit_denominator(10**8),Fraction(float(z)).limit_denominator(10**8)) for x,z in Pq]
    yf=[Fraction(float(v)).limit_denominator(10**8) for v in y]
    return planar.flow_lp(Qf,yf,strict=False).residual
def search(P,y,kap,rng,restarts=40):
    import itertools
    T=len(P); lo=P/kap; hi=P*kap; best=np.inf
    cand=[np.array(c,float).reshape(T,2) for c in itertools.product([0,1],repeat=2*T)]
    cand+= [rng.uniform(0,1,(T,2)) for _ in range(40*restarts)]
    # diagonal-ordered by level (heavy SW .. light NE), random monotone
    for _ in range(20*restarts):
        rank=rng.permutation(T)/max(T-1,1)
        cand.append(np.repeat(rank[:,None],2,axis=1))
    for s in cand:
        best=min(best,resid(lo+s*(hi-lo),y))
        if best<1e-9: break
    return best
if __name__=="__main__":
    rng=np.random.default_rng(int(sys.argv[1]));N=int(sys.argv[2]);Tmax=int(sys.argv[3])
    okhi=0;lowfound=0;tested=0;ndom=0
    for it in range(N):
        T=int(rng.integers(3,Tmax+1)); P=rng.uniform(0.5,4,(T,2)); y=np.round(rng.uniform(0,3,T),2)
        k=kappa_lp(P,y)
        from pair import rho_pair
        kd=float(np.exp(rho_pair(np.log(P),y)))
        assert k>=kd-1e-6,(k,kd)
        ndom+= abs(k-kd)<1e-6
        if k==1.0 or not np.isfinite(k): continue
        tested+=1
        eps=float(sys.argv[4]); bh=search(P,y,k*(1+eps),rng); bl=search(P,y,k*(1-eps),rng,restarts=15)
        okhi+= bh<1e-8; lowfound+= bl<1e-8
        print(it,T,"kappa*",round(k,4),"resid(+2%)",f"{bh:.2e}","resid(-2%)",f"{bl:.2e}",flush=True)
    print("kappa==kappa_dom in",ndom,"of",tested);print("tested",tested,"found above",okhi,"found below (bad)",lowfound)
