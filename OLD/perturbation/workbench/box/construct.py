"""Explicit construction of Q in the box from an LP solution (proof of sufficiency, executable).
1. LP at kappa gives flow f on the chain graph of W; decompose into paths -> reachable sets S_k of W with masses m_k.
2. K_k = conv(W \ S_k) + R^2_+ ; s_min_k(z) = min{s : z + s(1,1) in K_k}  (LP);  theta_k = clip(s_min_k/delta,0,1).
3. phi = sum m_k theta_k is continuous, antitone, phi|_W = w.  IVT on the diagonal of each box gives Q_t with phi(Q_t)=y_t.
4. phi = integral of indicators of complements of convex up-sets  =>  y weakly solvable at Q; verified by exact flow_lp."""
import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
from scipy.optimize import linprog
from lp_box import lp_box

def s_min(z,Tpts):
    """min s with  sum lam_j t_j <= z + s*(1,1), lam in simplex."""
    n=len(Tpts)
    if n==0: return np.inf
    c=np.zeros(n+1);c[-1]=1
    A=np.zeros((2,n+1));b=np.array(z,float)
    A[:,:n]=np.array(Tpts).T; A[:,-1]=-1
    res=linprog(c,A_ub=A,b_ub=b,A_eq=np.r_[np.ones(n),0][None,:],b_eq=[1],bounds=[(0,None)]*n+[(None,None)],method="highs")
    return res.fun

def construct(P,y,kappa):
    P=np.asarray(P,float);T=len(P)
    ok,fun,G,f,W=lp_box(P,y,kappa,return_sol=True)
    if not ok: return None
    Wf=np.array([[float(a),float(b)] for a,b in W])
    sets=[]
    for m,path in planar.decompose_flow(G,f):
        S=frozenset().union(*(G.arcs[k][2] for k in path)); sets.append((m,S))
    # margin delta
    info=[]
    delta=np.inf
    for m,S in sets:
        Tp=[Wf[q] for q in range(2*T) if q not in S]
        for q in S:
            sm=s_min(Wf[q],Tp)
            if np.isfinite(sm): delta=min(delta,sm)
        info.append((m,Tp))
    delta=min(delta,1.0)*0.5
    def phi(z):
        tot=0.0
        for m,Tp in info:
            sm=s_min(z,Tp); th=1.0 if not np.isfinite(sm) else min(1.0,max(0.0,sm/delta)); tot+=m*th
        return tot
    Q=np.zeros((T,2))
    for t in range(T):
        sw,ne=Wf[t],Wf[T+t]
        pt=lambda s: sw+s*(ne-sw)
        if phi(pt(0))<y[t]-1e-9 or phi(pt(1))>y[t]+1e-9: return ("IVT-bracket-fail",t,phi(pt(0)),phi(pt(1)),y[t])
        lo,hi=0.0,1.0
        for _ in range(60):
            mid=(lo+hi)/2
            if phi(pt(mid))>=y[t]: lo=mid
            else: hi=mid
        Q[t]=pt(lo)
    return Q
def resid_exact(Q,y):
    Qf=[(Fraction(float(x)).limit_denominator(10**12),Fraction(float(z)).limit_denominator(10**12)) for x,z in Q]
    yf=[Fraction(float(v)).limit_denominator(10**8) for v in y]
    return planar.flow_lp(Qf,yf,strict=False).residual
if __name__=="__main__":
    from lp_box import kappa_lp
    seed=int(sys.argv[1]);N=int(sys.argv[2]);Tmax=int(sys.argv[3]);eps=float(sys.argv[4])
    tested=ok=0
    for it in range(N):
        r=np.random.default_rng([seed,it]);T=int(r.integers(3,Tmax+1));P=r.uniform(0.5,4,(T,2));y=np.round(r.uniform(0,3,T),2)
        k=kappa_lp(P,y)
        if k==1.0: continue
        tested+=1; kap=k*(1+eps)
        Q=construct(P,y,kap)
        if isinstance(Q,tuple) or Q is None: print("FAIL",it,Q);continue
        inbox=(Q>=P/kap-1e-9).all() and (Q<=P*kap+1e-9).all()
        res=resid_exact(Q,y)
        good=inbox and res<1e-7
        ok+=good
        print(it,T,round(k,4),"inbox",inbox,"resid",f"{res:.1e}",flush=True)
    print("constructed+verified",ok,"of",tested)
