import sys,time,itertools
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as F
from exactbox import *
# (A) dominance only, arbitrary boxes, any d, exact rationals, zero-width coordinates
rng=np.random.default_rng(11);bad=0;N=0;feas=0
def dom_free(Q,y):
    T=len(Q);d=len(Q[0]);return all(any(Q[s][i]<=Q[t][i] for i in range(d)) for s in range(T) for t in range(T) if y[s]>y[t])
for it in range(3000):
    d=int(rng.integers(2,5));T=int(rng.integers(2,9));G=int(rng.integers(2,8))
    L=[tuple(F(int(v)) for v in rng.integers(0,G,d)) for _ in range(T)]
    U=[tuple(L[t][i]+F(int(rng.integers(0,3)))*F(int(rng.integers(0,2))) for i in range(d)) for t in range(T)]
    y=[int(v) for v in rng.integers(0,int(rng.integers(2,6)),T)]
    dec=dom_decide(L,U,y);N+=1
    if dec:
        feas+=1;Q=dom_witness(L,U,y)
        inb=all(L[t][i]<=Q[t][i]<=U[t][i] for t in range(T) for i in range(d))
        if not(inb and dom_free(Q,y)): bad+=1;print("WITNESS FAIL",L,U,y,Q)
    else:
        pass
print("dominance-only arbitrary boxes (d=2..4, zero-width coords): instances",N,"feasible",feas,"witness failures",bad)
# necessity: brute force on tiny instances (integer grid search over Q in box, d=2)
mism=0;M=0
for it in range(400):
    T=int(rng.integers(2,5));G=4
    L=[tuple(F(int(v)) for v in rng.integers(0,G,2)) for _ in range(T)]
    U=[tuple(L[t][i]+F(int(rng.integers(0,3))) for i in range(2)) for t in range(T)]
    y=[int(v) for v in rng.integers(0,3,T)]
    grids=[[(L[t][0]+a,L[t][1]+b) for a in range(int(U[t][0]-L[t][0])+1) for b in range(int(U[t][1]-L[t][1])+1)] for t in range(T)]
    found=any(dom_free(list(Q),y) for Q in itertools.product(*grids))
    M+=1; mism+= (found!=dom_decide(L,U,y))
print("dominance-only vs integer-grid brute force:",M,"instances, mismatches",mism)
