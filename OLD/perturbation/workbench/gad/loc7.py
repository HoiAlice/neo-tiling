"""Block certificates with violation credits.
milp_credit(sw, rel, time_limit): min over ALL routings (switch bits free) of  cost - sum_l credit_l * viol_l,
 rel = list of (i, j, kind, credit), kind 'eq' (required equal bits) or 'ne' (required different bits), i,j block-local indices.
sat_value: min cost with all relations satisfied.
Both use tangent-cut MILP (valid lower bounds, grid error ~1e-5)."""
import sys, math, numpy as np
import cx2
from core import CP
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
from iso_scipy import iso_cost

def build(sw, rel, force_sat=False):
    A_, Y, conf, ks = cx2.setup(sw)
    T = len(A_); C = len(conf); nu = 2*T; ng = 2*T; nz = C; nw = len(rel)
    n = nu+ng+nz+nw
    rows=[]; lo=[]; hi=[]
    M = lil_matrix((len(CP)*ng + 4*C + 4*nw + 4*nw + 10, n)); r=0
    for t in range(T):
        for i in range(2):
            ui=2*t+i; gi=nu+ui
            for d0 in CP:
                s=1 if d0>=0 else -1; e=math.exp(abs(d0))
                M[r,gi]=1; M[r,ui]=-e*s
                lo.append(e*(1-s*d0)-1-e*s*A_[t][i]); hi.append(np.inf); r+=1
    BIG=40.0
    for k,(t,s) in enumerate(conf):
        zi=nu+ng+k
        for i in range(2):
            ut=2*t+i; us=2*s+i
            M[r,ut]=1; M[r,us]=-1
            if i==1: M[r,zi]=BIG; lo.append(-np.inf); hi.append(BIG)
            else: M[r,zi]=-BIG; lo.append(-np.inf); hi.append(0.0)
            r+=1
    for l,(a,b,kind,cr) in enumerate(rel):
        za=nu+ng+ks[a]; zb=nu+ng+ks[b]; wi=nu+ng+nz+l
        if force_sat:
            # equality of bits
            M[r,za]=1; M[r,zb]= -1 if kind=='eq' else 1
            v = 0.0 if kind=='eq' else 1.0
            lo.append(v); hi.append(v); r+=1
        else:
            if kind=='eq':   # viol = [za != zb]: w<=za+zb ; w<=2-za-zb
                M[r,wi]=1; M[r,za]=-1; M[r,zb]=-1; lo.append(-np.inf); hi.append(0.0); r+=1
                M[r,wi]=1; M[r,za]=1; M[r,zb]=1; lo.append(-np.inf); hi.append(2.0); r+=1
            else:            # viol = [za == zb]: w<=1-za+zb ; w<=1+za-zb
                M[r,wi]=1; M[r,za]=1; M[r,zb]=-1; lo.append(-np.inf); hi.append(1.0); r+=1
                M[r,wi]=1; M[r,za]=-1; M[r,zb]=1; lo.append(-np.inf); hi.append(1.0); r+=1
    M=M[:r].tocsr()
    c=np.zeros(n); c[nu:nu+ng]=1
    for l,(a,b,kind,cr) in enumerate(rel): c[nu+ng+nz+l]=-cr
    lb=np.full(n,-np.inf); ub=np.full(n,np.inf)
    for t in range(T):
        for i in range(2): lb[2*t+i]=A_[t][i]-4; ub[2*t+i]=A_[t][i]+4
    lb[nu:nu+ng]=0; ub[nu:nu+ng]=60; lb[nu+ng:]=0; ub[nu+ng:]=1
    integ=np.zeros(n); integ[nu+ng:]=1
    if force_sat: ub[nu+ng+nz:]=0
    return c,M,lo,hi,lb,ub,integ,(A_,Y,conf,ks)

def run(sw, rel, force_sat=False, time_limit=600):
    c,M,lo,hi,lb,ub,integ,info=build(sw,rel,force_sat)
    res=milp(c,constraints=LinearConstraint(M,lo,hi),bounds=Bounds(lb,ub),integrality=integ,
             options=dict(time_limit=time_limit,mip_rel_gap=1e-9))
    return res

def milp_credit(sw,rel,time_limit=600):
    r=run(sw,rel,False,time_limit); return r.fun, getattr(r,'mip_dual_bound',None), r.status
def sat_value(sw,rel,time_limit=600):
    r=run(sw,rel,True,time_limit); return r.fun, getattr(r,'mip_dual_bound',None), r.status
