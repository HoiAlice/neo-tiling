import sys,time,itertools
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as F
from scipy.optimize import linprog
from exactbox import *
rng=np.random.default_rng(int(sys.argv[1]));mode=sys.argv[2];N=int(sys.argv[3])
if mode=="cone":     # planar.py flow LP vs definition (brute-force family), duplicates / collinear / aligned points
    bad=0;nsol=0;dup=0
    for it in range(N):
        T=int(rng.integers(2,7));G=int(rng.integers(2,5))
        P=[(F(int(a)),F(int(b))) for a,b in rng.integers(1,G+1,(T,2))]
        if len(set(P))<T: dup+=1
        y=[int(v) for v in rng.integers(0,4,T)]
        fam=planar.family(P,strict=False)
        M=np.array([[1.0 if q in S else 0.0 for S in fam] for q in range(T)])
        r=linprog(np.zeros(len(fam)),A_eq=M,b_eq=np.array(y,float),bounds=[(0,None)]*len(fam),method="highs")
        a=(r.status==0); b=planar.flow_lp(P,[F(v) for v in y],strict=False).feasible
        nsol+=a
        if a!=b: bad+=1;print("MISMATCH",P,y,a,b)
    print("cone vs flow LP (weak) on degenerate planar sets:",N,"instances (with duplicate points:",dup,"), solvable",nsol,", mismatches",bad)
else:
    st=dict(n=0,true=0,false=0,delta_dis=0,grid_viol=0,constr_ok=0,constr_bad=0,grid_witness_missing=0)
    for it in range(N):
        T=int(rng.integers(2,6));G=int(rng.integers(2,6))
        L=[tuple(F(int(v)) for v in rng.integers(1,G+1,2)) for _ in range(T)]
        U=[tuple(L[t][i]+F(int(rng.integers(0,3)))*F(int(rng.integers(0,2))) for i in range(2)) for t in range(T)]
        y=[F(int(v)) for v in rng.integers(0,int(sys.argv[4]),T)]
        a=decide_closed(L,U,y);st['n']+=1;st['true']+=a;st['false']+=(not a)
        if a!=decide(L,U,y): st['delta_dis']+=1;print("DELTA vs CLOSED",L,U,y)
        if a:
            Q=construct_closed(L,U,y)
            inb=all(L[t][i]<=Q[t][i]<=U[t][i] for t in range(T) for i in range(2))
            ok=inb and certify_Q(Q,y);st['constr_ok']+=ok;st['constr_bad']+=(not ok)
            if not ok: print("CONSTRUCTION FAIL",L,U,y,Q)
        else:
            if T<=4:
                grids=[[(L[t][0]+F(p,4),L[t][1]+F(q,4)) for p in range(int(4*(U[t][0]-L[t][0]))+1) for q in range(int(4*(U[t][1]-L[t][1]))+1)] for t in range(T)]
                if np.prod([len(g) for g in grids])<=20000:
                    if any(planar.flow_lp(list(Q),y,strict=False).feasible for Q in itertools.product(*grids)): st['grid_viol']+=1;print("GRID WITNESS BUT LP(0) FALSE",L,U,y)
    print(st)
