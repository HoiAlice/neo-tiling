"""Fixed-xi convex (LP w/ tangent cuts) cost for two-class instances; landscape over xi."""
import numpy as np, itertools
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
# cost per coordinate: a in (0,inf): g>=a-1, g>=1/a-1 (tangents at a_k)
TAN=np.concatenate([np.linspace(0.2,1,40),np.linspace(1,5,60)[1:]])
def lp_cost(P, heavy, light, xi):
    """xi: dict heavy-> lam in [0,1]. returns min cost; vars a(t,i) for all t,i then g(t,i)."""
    T=len(P); n=2*T
    # var index: a: 2t+i ; g: n+2t+i
    c=np.zeros(2*n); c[n:]=1
    A=[];b=[]
    for k in range(n):
        # g>=a-1 -> a-g<=1
        r=np.zeros(2*n); r[k]=1; r[n+k]=-1; A.append(r); b.append(1)
        for ak in TAN:
            # 1/a-1 >= 1/ak -1 - (a-ak)/ak^2  => g >= 2/ak -1 - a/ak^2 -> -a/ak^2 - g <= 1-2/ak
            r=np.zeros(2*n); r[k]=-1/ak**2; r[n+k]=-1; A.append(r); b.append(1-2/ak)
    for h in heavy:
        lam=xi[h]; w=(lam,1-lam)
        for l in light:
            # sum_i w_i (P[l,i] a[l,i] - P[h,i] a[h,i]) >=0 -> -(...)<=0
            r=np.zeros(2*n)
            for i in range(2):
                r[2*l+i]-=w[i]*P[l,i]; r[2*h+i]+=w[i]*P[h,i]
            A.append(r); b.append(0)
    bounds=[(0.05,20)]*n+[(0,None)]*n
    res=linprog(c,A_ub=np.array(A),b_ub=np.array(b),bounds=bounds,method="highs")
    return res.fun if res.status==0 else np.inf
