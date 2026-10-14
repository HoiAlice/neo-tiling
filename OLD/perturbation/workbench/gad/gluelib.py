import numpy as np, itertools, math, cx2
from iso_scipy import iso_cost
from snapw import snap
import planar
from fractions import Fraction
H=4*math.log(21/20)
cx2.EPS=H
def B(d): return 2*(math.exp(d*H/2)-1)
def rule_levels(sw,kinks,c1=0.02,Delta=0.6,g=0.002,eps=0.3):
    """sw: list (bx,by,d) -> list (bx,by,d,ytop,ybot) with the final y-rule of WEAK-SOLV 13"""
    sc=[bx+by+d for (bx,by,d) in sw]
    smax=max(sc)+1
    def F(s):
        # slope c1 below first kink, +Delta at each kink (steeper toward NE)
        val=1+c1*(smax-s)
        for k in kinks: val+=Delta*max(0.0,min(smax,smax)-max(s,k)) if True else 0
        return val
    Fv=[F(s) for s in sc]
    top=[f+g for f in Fv]
    m=max(top)
    out=[]
    for (bx,by,d),f in zip(sw,Fv):
        out.append((bx,by,d,1+eps*(f+g)/m,1+eps*f/m))
    return out
def setup(swl):
    return cx2.setup(swl)
def glue(A,conf,ks,sig,tol=1e-7,maxit=60):
    own={k:sig[i] for i,k in enumerate(ks)}; assign=dict(own)
    for it in range(maxit):
        edges=[[],[]]
        for k,c in assign.items(): edges[c].append(conf[k])
        c0,u0=iso_cost(A[:,0],edges[0]); c1,u1=iso_cost(A[:,1],edges[1])
        u=np.column_stack([u0,u1]); viol=[]
        for k,(t,s) in enumerate(conf):
            if k in assign: continue
            d0=u[t,0]-u[s,0]; d1=u[t,1]-u[s,1]
            if d0>tol and d1>tol: viol.append((k,0 if d0<=d1 else 1,min(d0,d1)))
        if not viol: break
        viol.sort(key=lambda x:-x[2])
        for k,c,_ in viol[:max(1,len(viol)//3+1)]: assign[k]=c
    nv=sum(1 for (t,s) in conf if u[t,0]-u[s,0]>tol and u[t,1]-u[s,1]>tol)
    return u,c0+c1,nv
def weak(Q,y,graph=None):
    Pf=[tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q]
    yf=[Fraction(float(v)).limit_denominator(10**9) for v in y]
    g=graph or planar.chain_graph(Pf)
    return planar.flow_lp(Pf,yf,graph=g).feasible
