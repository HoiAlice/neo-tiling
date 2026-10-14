"""Degenerate-P construction: LP(P,kappa) feasible  =>  Q in box of kappa2 > kappa with y weakly solvable (no genericity).
Sets: Out-sets of flow paths (+ boundary additions as planar.certify), masses by NNLS to the LP vector w."""
import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
from scipy.optimize import nnls
from lp_box import lp_box, kappa_lp, W_points
from construct import s_min, resid_exact

def construct2(P,y,kappa,kappa2):
    P=np.asarray(P,float);T=len(P)
    ok,fun,G,f,W=lp_box(P,y,kappa,return_sol=True)
    if not ok: return None
    Wf=np.array([[float(a),float(b)] for a,b in W]); n2=2*T
    cand=set()
    for m,path in planar.decompose_flow(G,f):
        out=frozenset().union(*(G.arcs[k][2] for k in path)); bnd=frozenset().union(*(G.arcs[k][3] for k in path))
        cand.add(out)
        bl=sorted(bnd)
        for j in range(1,len(bl)+1):
            for sub in __import__('itertools').combinations(bl,j): cand.add(out|frozenset(sub))
    cand=[S for S in cand if planar.is_reachable(W,sorted(S),strict=False)]
    # LP vector w = Out-part of flow + g ; recompute from LP: use y-row identity w_q = sum_f 1[q in Out] + g ; approximate g by NNLS fit to bounds
    w=np.zeros(n2)
    for k,(_,_,out,_) in enumerate(G.arcs):
        for q in out: w[q]+=f[k]
    # g unknown here: fit sets to the target interval [y at SW, y at NE] : find m>=0 with M m >= y(SW), M m <= y(NE)
    from scipy.optimize import linprog
    M=np.array([[1.0 if q in S else 0.0 for S in cand] for q in range(n2)])
    A=np.vstack([-M[:T],M[T:]]);b=np.concatenate([-np.asarray(y,float),np.asarray(y,float)])
    res=linprog(np.zeros(len(cand)),A_ub=A,b_ub=b,bounds=[(0,None)]*len(cand),method="highs")
    if res.status!=0: return ("no-cover-by-candidate-sets",len(cand))
    ms=res.x
    info=[(m,[Wf[q] for q in range(n2) if q not in S],S) for m,S in zip(ms,cand) if m>1e-13]
    W2=np.array([[float(a),float(b)] for a,b in W_points(P,kappa2)])
    delta=1.0
    for m,Tp,S in info:
        for t in range(T):
            if t in S:
                sm=s_min(W2[t],Tp)  # SW'' corner of an S point
                if np.isfinite(sm): delta=min(delta,sm)
            if (T+t) not in S:
                sm=s_min(W2[T+t],Tp); delta=min(delta,-sm)
    if delta<=0: return ("margin-nonpositive",delta)
    delta*=0.5
    def phi(z):
        tot=0.0
        for m,Tp,S in info:
            sm=s_min(z,Tp);th=1.0 if not np.isfinite(sm) else min(1.0,max(0.0,sm/delta));tot+=m*th
        return tot
    Q=np.zeros((T,2))
    for t in range(T):
        sw,ne=W2[t],W2[T+t];pt=lambda s: sw+s*(ne-sw)
        if phi(pt(0))<y[t]-1e-9 or phi(pt(1))>y[t]+1e-9: return ("IVT-fail",t)
        lo,hi=0.0,1.0
        for _ in range(60):
            mid=(lo+hi)/2
            if phi(pt(mid))>=y[t]: lo=mid
            else: hi=mid
        Q[t]=pt(lo)
    return Q
if __name__=="__main__":
    seed=int(sys.argv[1]);N=int(sys.argv[2]);Tmax=int(sys.argv[3]);G=int(sys.argv[4]);tested=ok=0
    for it in range(N):
        r=np.random.default_rng([seed,it]);T=int(r.integers(3,Tmax+1));P=r.integers(1,G+1,(T,2)).astype(float);y=r.integers(0,4,T).astype(float)
        k=kappa_lp(P,y,iters=45)
        if k==1.0 or not np.isfinite(k): continue
        tested+=1;k1=k*(1+1e-4);k2=k*(1+2e-3)
        Q=construct2(P,y,k1,k2)
        if Q is None or isinstance(Q,tuple): print("FAIL",it,Q,P.tolist(),y.tolist(),flush=True);continue
        inbox=(Q>=P/k2-1e-9).all() and (Q<=P*k2+1e-9).all();res=resid_exact(Q,y)
        ok+= inbox and res<1e-7
        if not(inbox and res<1e-7): print("BAD",it,inbox,res,flush=True)
    print("grid instances G=%d: constructed+verified %d of %d"%(G,ok,tested))
