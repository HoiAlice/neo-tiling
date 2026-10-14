"""Farkas certificate on the minimal obstruction of the two-copy layout."""
import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar, itertools
from fractions import Fraction
from scipy.optimize import linprog
import ws_two as W
from ws_p9 import minimal_switches
from core import weakly_solvable
def farkas(Q,y):
    P=[tuple(Fraction(float(v)).limit_denominator(10**9) for v in r) for r in Q]
    fam=[S for S in planar.family(P)]   # all weakly reachable sets (strict=False default? check)
    n=len(y); M=np.array([[1.0 if i in S else 0.0 for i in range(n)] for S in fam])
    # min lam.y  s.t. M lam >= 0, -1<=lam<=1
    r=linprog(y,A_ub=-M,b_ub=np.zeros(len(fam)),bounds=[(-1,1)]*n,method="highs")
    return r.x,r.fun,len(fam)
if __name__=="__main__":
    eps=0.3; y=W.y_multi(W.K,W.SL,eps); pi=W.pats.index([0,1,0,1])
    Q=W.Qcat(pi,pi); k,P=minimal_switches(Q,y); print("min switches",k,"points",len(P))
    lam,val,nf=farkas(Q[P],y[P]); print("reachable sets",nf,"min lam.y",val)
    A=np.vstack([np.load("ws_snap_cp.npz")['A']]*2)/0.2; A[2*W.n1:]+=W.D
    for a,p in zip(lam,P):
        if abs(a)>1e-6:
            sw_i=p//2; print("  lam %+.3f"%a,"c%d s%d%s"%(p//(2*W.n1),sw_i%W.n1,"t" if p%2==0 else "b"),"point (x,y)=(%.2f,%.2f) s=%.2f t=%.2f"%(A[p,0],A[p,1],A[p].sum(),A[p,1]-A[p,0]),"s_c",int(W.s[sw_i]),"y %.4f"%y[p])
