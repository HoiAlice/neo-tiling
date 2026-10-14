"""Largest top-gap t such that y = F + t*tau is weakly solvable at Q (flow LP with t a variable). F fixed (point values), tau = 1 on tops."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def gmax(Q,F,tau,tcap=1.0,return_dual=False):
    T=len(F); G=planar.chain_graph([tuple(Fraction(float(v)).limit_denominator(10**9) for v in r) for r in Q])
    A=len(G.arcs); nv=A+T+1; tv=nv-1; idx={n:k for k,n in enumerate(G.nodes)}; n_int=len(G.nodes)
    Aeq=lil_matrix((n_int+T,nv)); beq=np.zeros(n_int+T); Aub=lil_matrix((T,nv))
    for k,(u,v,out,bnd) in enumerate(G.arcs):
        if u in idx: Aeq[idx[u],k]-=1
        if v in idx: Aeq[idx[v],k]+=1
        for q in out: Aeq[n_int+q,k]+=1
        for q in bnd: Aub[q,k]-=1
    for q in range(T):
        Aeq[n_int+q,A+q]+=1; Aeq[n_int+q,tv]-=tau[q]; beq[n_int+q]=F[q]
        Aub[q,A+q]+=1
    c=np.zeros(nv); c[tv]=-1
    r=linprog(c,A_ub=Aub.tocsr(),b_ub=np.zeros(T),A_eq=Aeq.tocsr(),b_eq=beq,bounds=[(0,None)]*(nv-1)+[(0,tcap)],method="highs")
    if r.status!=0: return None
    return r.x[tv] if not return_dual else (r.x[tv], np.asarray(r.eqlin.marginals[n_int:]))
