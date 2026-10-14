import numpy as np, cx2, itertools
from scipy.optimize import minimize
B=2*(np.exp(0.4)-1); J=2*(np.exp(0.1)-1)
def chain(n,a=3): return [(a*i,-a*i,4,2,1) for i in range(n)]
def fixed_cost(A,conf,coord,w=None,subset=None):
    """min weighted cost with each conflict k forced into coordinate coord[k]; subset: indices of conflicts kept"""
    T=len(A); w=np.ones(T) if w is None else w
    x0=A.flatten(); W=np.repeat(w,2)
    f=lambda x:np.sum(W*(np.exp(np.abs(x-x0))-1)); fp=lambda x:W*np.exp(np.abs(x-x0))*np.sign(x-x0)
    cons=[]
    for k,((t,s),i) in enumerate(zip(conf,coord)):
        if subset is not None and k not in subset: continue
        v=np.zeros(2*T); v[2*s+i]=1; v[2*t+i]=-1
        cons.append({"type":"ineq","fun":lambda x,v=v:v@x,"jac":lambda x,v=v:v})
    r=minimize(f,x0,jac=fp,constraints=cons,method="SLSQP",options=dict(ftol=1e-15,maxiter=3000))
    return r.fun
# (a) y-route: all cross conflicts forced into coordinate 1 (y) for sigma all y (=1)
for n in range(2,7):
    A,Y,conf,ks=cx2.setup(chain(n))
    own=set(ks)
    # own pairs coordinate 1; cross: all coordinate 1 (y-route)
    coord=[1]*len(conf)
    cy=fixed_cost(A,conf,coord)
    # best route: cross free via MILP would give nB+(n-1)J
    print(n,"y-route cost",round(cy,5),"nB+(n-1)J",round(n*B+(n-1)*J,5),"extra per link",round((cy-n*B)/(n-1),4),"J",round(J,4))
