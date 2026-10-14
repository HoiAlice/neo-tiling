"""Exact BOXdom: min r s.t. exists u in boxes (sup-norm radius r around a) with dominance-free y-order. MILP (HiGHS)."""
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

def conflicts(y):
    T=len(y); return [(a,b) for a in range(T) for b in range(T) if y[a]>y[b]]

def rho_exact(a, y, want_u=False, rfix=None):
    a=np.asarray(a,float); T=len(a); C=conflicts(y); nC=len(C)
    if nC==0: return (0.0,a.copy(),[]) if want_u else 0.0
    n=2*T+1+nC; ir=2*T
    M=float(np.ptp(a))+10.0
    A=lil_matrix((4*T+2*nC,n)); lo=[];hi=[]; k=0
    for t in range(T):
        for i in range(2):
            A[k,2*t+i]=1;A[k,ir]=-1;lo.append(-np.inf);hi.append(a[t,i]);k+=1   # u-r<=a
            A[k,2*t+i]=1;A[k,ir]=1;lo.append(a[t,i]);hi.append(np.inf);k+=1      # u+r>=a
    for c,(p,q) in enumerate(C):
        z=2*T+1+c
        A[k,2*p]=1;A[k,2*q]=-1;A[k,z]=-M;lo.append(-np.inf);hi.append(0);k+=1       # z=0 -> x ok
        A[k,2*p+1]=1;A[k,2*q+1]=-1;A[k,z]=M;lo.append(-np.inf);hi.append(M);k+=1    # z=1 -> y ok
    cost=np.zeros(n);cost[ir]=1
    lb=np.full(n,-np.inf);ub=np.full(n,np.inf);lb[ir]=0;ub[ir]=M
    if rfix is not None: lb[ir]=ub[ir]=rfix
    lb[2*T+1:]=0;ub[2*T+1:]=1
    integ=np.zeros(n);integ[2*T+1:]=1
    res=milp(cost,constraints=LinearConstraint(A.tocsr()[:k],lo,hi),bounds=Bounds(lb,ub),integrality=integ,options=dict(mip_rel_gap=1e-9,time_limit=60))
    if res.x is None: return None
    r=res.x[ir]
    if want_u: return r,res.x[:2*T].reshape(T,2),[int(round(v)) for v in res.x[2*T+1:]]
    return r
if __name__=="__main__":
    P=np.array([[4,1],[3,3],[1,4]],float);y=[1,5,3]
    print(rho_exact(P,y,True))
