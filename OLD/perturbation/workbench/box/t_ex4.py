import sys,time,itertools
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as F
from exactbox import *
rng=np.random.default_rng(int(sys.argv[1]));N=int(sys.argv[2]);t0=time.time()
st=dict(n=0,lp_true=0,grid_found=0,viol=0,const_viol=0,constr=0,constr_ok=0,lp_true_nogrid=0)
for it in range(N):
    T=int(rng.integers(2,5));G=5
    L=[tuple(F(int(v)) for v in rng.integers(1,G,2)) for _ in range(T)]
    U=[tuple(L[t][i]+F(int(rng.integers(0,3)))*F(int(rng.integers(0,2))) for i in range(2)) for t in range(T)]
    y=[F(int(v)) for v in rng.integers(0,int(sys.argv[3]),T)]
    d=delta_bound(L,U);lp=decide(L,U,y,d);st['n']+=1;st['lp_true']+=lp
    lp2=decide(L,U,y,d/1000)
    if lp2!=lp: st['const_viol']+=1
    # grid oracle with half-integer grid
    grids=[[(L[t][0]+F(a,2),L[t][1]+F(b,2)) for a in range(int(2*(U[t][0]-L[t][0]))+1) for b in range(int(2*(U[t][1]-L[t][1]))+1)] for t in range(T)]
    found=False
    for Q in itertools.product(*grids):
        if planar.flow_lp(list(Q),y,strict=False).feasible: found=True;break
    st['grid_found']+=found
    if found and not lp: st['viol']+=1;print("VIOLATION grid witness but LP false",L,U,y)
    if lp and not found: st['lp_true_nogrid']+=1
    if lp:
        Qc=construct(L,U,y,2*d);st['constr']+=1
        st['constr_ok']+= all(L[t][i]-2*d<=Qc[t][i]<=U[t][i]+2*d for t in range(T) for i in range(2)) and certify_Q(Qc,y)
print(st,"time %.0fs"%(time.time()-t0))
