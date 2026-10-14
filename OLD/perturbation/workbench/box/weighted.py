"""Per-coordinate tolerances: log-radius r_ti = lam*w_ti.  Theorem 1': BOXdom iff for all y_s>y_t exists i: a_si - a_ti <= lam (w_si+w_ti).
Witness: u_t = SW_t + tau_t (NE_t-SW_t), tau_t = clip(max_{s:y_s>y_t} min_i (SW_si-SW_ti)/(NE_ti-SW_ti), 0, 1)."""
import numpy as np, sys
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
def lam_dom(a,y,w):
    T=len(a);best=0.0
    for s in range(T):
        for t in range(T):
            if y[s]>y[t]: best=max(best,min((a[s,i]-a[t,i])/(w[s,i]+w[t,i]) for i in range(2)))
    return best
def witness(a,y,lam,w):
    T=len(a);r=lam*w;SW=a-r;NE=a+r;u=np.zeros((T,2))
    for t in range(T):
        tau=0.0
        for s in range(T):
            if y[s]>y[t]: tau=max(tau,min((SW[s,i]-SW[t,i])/(NE[t,i]-SW[t,i]) for i in range(2)))
        u[t]=SW[t]+min(1.0,tau)*(NE[t]-SW[t])
    return u
def feasible_milp(a,y,r):
    """decision MILP with per-coordinate radii r (T,2)"""
    T=len(a);C=[(p,q) for p in range(T) for q in range(T) if y[p]>y[q]];nC=len(C)
    M=float(np.ptp(a))+2*r.max()+5;n=2*T+nC;A=lil_matrix((2*nC,n));hi=[];k=0
    for c,(p,q) in enumerate(C):
        z=2*T+c
        A[k,2*p]=1;A[k,2*q]=-1;A[k,z]=-M;hi.append(0);k+=1
        A[k,2*p+1]=1;A[k,2*q+1]=-1;A[k,z]=M;hi.append(M);k+=1
    lb=np.concatenate([(a-r).ravel(),np.zeros(nC)]);ub=np.concatenate([(a+r).ravel(),np.ones(nC)])
    integ=np.concatenate([np.zeros(2*T),np.ones(nC)])
    if nC==0: return True
    res=milp(np.zeros(n),constraints=LinearConstraint(A.tocsr(),-np.inf,hi),bounds=Bounds(lb,ub),integrality=integ)
    return res.x is not None
def dom_free(u,y,tol=1e-9):
    T=len(u);return all((u[p]<=u[q]+tol).any() for p in range(T) for q in range(T) if y[p]>y[q])
if __name__=="__main__":
    rng=np.random.default_rng(7);bad=0;N=300
    for it in range(N):
        T=int(rng.integers(3,11));a=rng.uniform(0,6,(T,2));y=rng.integers(0,int(rng.integers(2,7)),T).astype(float);w=rng.uniform(0.2,2,(T,2))
        lam=lam_dom(a,y,w)
        u=witness(a,y,lam,w);ok=dom_free(u,y) and (np.abs(u-a)<=lam*w+1e-9).all()
        m1=feasible_milp(a,y,lam*w*(1+1e-7)); m0=feasible_milp(a,y,lam*w*(1-1e-3)) if lam>1e-6 else False
        if not(ok and m1 and not m0): bad+=1;print("BAD",it,ok,m1,m0)
    print("weighted dom:",N,"instances, failures",bad)
