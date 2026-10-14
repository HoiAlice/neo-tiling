"""Necessity test: build (Q,y) with y weakly solvable at Q, perturb P in a box of log-radius r0; LP kappa* must be <= exp(r0)."""
import sys, itertools
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
from lp_box import kappa_lp
rng=np.random.default_rng(int(sys.argv[1]));N=int(sys.argv[2])
viol=0;strict=0
for it in range(N):
    T=int(rng.integers(3,7))
    Q=rng.uniform(0.3,3,(T,2))
    Qf=[(Fraction(x).limit_denominator(10**6),Fraction(z).limit_denominator(10**6)) for x,z in Q]
    # random reachable sets
    y=np.zeros(T);cnt=0
    for _ in range(40):
        S=[t for t in range(T) if rng.random()<0.5]
        if S and len(S)<T and planar.is_reachable(Qf,S): 
            y[S]+=rng.uniform(0.2,1.5);cnt+=1
    if cnt==0: y[:]=1
    r0=rng.uniform(0.02,0.4)
    P=Q*np.exp(rng.uniform(-r0,r0,(T,2)))
    k=kappa_lp(P,y)
    if k>np.exp(r0)*(1+1e-6): viol+=1; print("VIOLATION",k,np.exp(r0))
    if k<np.exp(r0)*0.98: strict+=1
print("N",N,"violations",viol,"strictly-below(slack)",strict)
