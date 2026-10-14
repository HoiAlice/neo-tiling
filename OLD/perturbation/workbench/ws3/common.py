import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad")
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
import planar
from ws_rule import build, sc
def kinked_y(sw, kinks, rho=11.0, c1=0.02, gfac=0.1, eps=0.3):
    s=sc(sw); smax=s.max()
    def slope(v): return c1*rho**sum(1 for q in kinks if v>q)
    def F(v):
        val=0.0; cuts=[-1e9]+list(kinks)+[1e9]
        for i in range(len(kinks)+1):
            lo=max(cuts[i],v); hi=min(cuts[i+1],smax)
            if hi>lo: val+=c1*rho**i*(hi-lo)
        return val
    fb=np.array([F(v) for v in s]); gap=np.array([gfac*slope(v) for v in s])
    eta=np.concatenate([[b+g_,b] for b,g_ in zip(fb,gap)])
    # M=1+eps*max ... y = 1+eps*eta/max ; gaps scale likewise
    m=eta.max()
    return 1+eps*eta/m, eps*gap/m
def feasible(Q,y):
    P=[tuple(map(float,q)) for q in Q]
    r=planar.flow_lp(P,np.asarray(y,float))
    return r
def quad_sets(Q, tol=1e-9):
    """for each switch i (points 2i top, 2i+1 bottom): bit type and S_t indicator (bool over points)"""
    L=np.log(Q); n=len(Q)//2; out=[]
    for i in range(n):
        top,bot=L[2*i],L[2*i+1]
        typ='x' if abs(top[0]-bot[0])<tol else ('y' if abs(top[1]-bot[1])<tol else '?')
        inT=np.zeros(len(Q),bool)
        for p in range(len(Q)):
            d=L[p]-bot
            if (abs(d[0])<tol and abs(d[1])<tol) or (d[0]>tol and d[1]>tol): inT[p]=True
        inT[2*i+1]=True
        out.append((typ,~inT))
    return out
