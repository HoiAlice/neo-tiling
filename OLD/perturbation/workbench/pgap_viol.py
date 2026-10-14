"""Route A certificate: for each of the 6 pairs (a,b) in C\\C^P and each U-phase, lower-bound the cost of any price system that
is feasible for C_sym and VIOLATES the pair (Q_a > Q_b in both coords, margin MARG). MILP with tangent cuts => valid lower bound.
Compare with E_sym (MILP on C_sym) of the same phase."""
import sys, math
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad")
from yv2 import *
import cx2
from multiprocessing import Pool
nU,nV=4,5
sw=build4(nU,nV,3,4,1,5,0.05,0.05,0.2)
A,Y,conf,ks=cx2.setup(sw)
names=[]
for j in range(nU): names+= [f"Ut{j+1}",f"Ub{j+1}"]
for s in range(-2,3): names+= [f"Vt{s}",f"Vb{s}"]
ix={n:i for i,n in enumerate(names)}
def tau(n):
    k,i=n[:2],n[2:]
    if k[0]=='U': return ('Ub' if k[1]=='t' else 'Ut')+str(5-int(i))
    return ('Vb' if k[1]=='t' else 'Vt')+str(-int(i))
full=[(t,s) for t in range(len(Y)) for s in range(len(Y)) if Y[t]>Y[s]]
C=set((names[t],names[s]) for t,s in full)
CP=set((tau(b),tau(a)) for a,b in C)
asym=sorted(C-CP)
csym=[(ix[a],ix[b]) for (a,b) in sorted(C&CP)]
MARG=1e-6
def solve(args):
    phi,pair=args
    # build MILP: reuse solve_dom by augmenting via monkeypatched conflicts: violation = two hard rows. Do it by own copy.
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import lil_matrix
    conflicts=csym
    T=len(A);a=A
    C_=len(conflicts); nu=2*T; ng=2*T; n=nu+ng+C_
    A_=lil_matrix((len(CP_)*ng+4*C_+10,n)); lo=[];hi=[];r=0
    for t in range(T):
        for i in range(2):
            ui=2*t+i; gi=nu+ui
            for d0 in CP_:
                s=1 if d0>=0 else -1; e=math.exp(abs(d0))
                A_[r,gi]=1; A_[r,ui]=-e*s
                lo.append(e*(1-s*d0)-1-e*s*a[t][i]); hi.append(np.inf); r+=1
    M=40.0
    for k,(t,s) in enumerate(conflicts):
        zi=nu+ng+k
        for i in range(2):
            ut=2*t+i; us=2*s+i
            A_[r,ut]=1; A_[r,us]=-1
            if i==1: A_[r,zi]=M; lo.append(-np.inf); hi.append(M)
            else: A_[r,zi]=-M; lo.append(-np.inf); hi.append(0.0)
            r+=1
    if pair is not None:
        pa,pb=ix[pair[0]],ix[pair[1]]
        for i in range(2):   # u_pa,i - u_pb,i >= MARG  (violation of N)
            A_[r,2*pa+i]=1; A_[r,2*pb+i]=-1; lo.append(MARG); hi.append(np.inf); r+=1
    A_=A_[:r].tocsr()
    c=np.zeros(n); c[nu:nu+ng]=1
    lb=np.full(n,-np.inf); ub=np.full(n,np.inf)
    for t in range(T):
        for i in range(2): lb[2*t+i]=a[t][i]-4; ub[2*t+i]=a[t][i]+4
    lb[nu:nu+ng]=0; ub[nu:nu+ng]=60; lb[nu+ng:]=0; ub[nu+ng:]=1
    # designated switch bits: end switches fixed by phase (sigma of (top,bottom) of U_1,U_4: phi, 1-phi), V uniform 0 on ends; interior free.
    cidx={c_:k for k,c_ in enumerate(conflicts)}
    fx={0:phi,nU-1:1-phi,nU:0,nU+nV-1:0}
    for sidx,v in fx.items(): lb[nu+ng+cidx[(2*sidx,2*sidx+1)]]=ub[nu+ng+cidx[(2*sidx,2*sidx+1)]]=v
    integ=np.zeros(n); integ[nu+ng:]=1
    res=milp(c,constraints=LinearConstraint(A_,lo,hi),bounds=Bounds(lb,ub),integrality=integ,options=dict(time_limit=900,mip_rel_gap=1e-7))
    return phi,pair,(res.fun if res.x is not None else None),res.mip_dual_bound if hasattr(res,'mip_dual_bound') else None
CP_=cx2.CP
if __name__=="__main__":
    jobs=[(phi,None) for phi in (0,1)]+[(phi,p) for phi in (0,1) for p in asym]
    with Pool(5) as p:
        for out in p.imap(solve,jobs):
            print(out,flush=True)
