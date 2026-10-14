"""Exact pointwise moderate-witness test.  For t in S: exists xi>=0 nonzero with xi.(Q_s-Q_t)>=0 for s in T and for the two ghosts of t (NW: (delta, y_t e^ell), SE: (x_t e^ell, delta))."""
import sys,os,time; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from fractions import Fraction as Fr
from ws_exact import y_rational
from ws_exact2 import certify2, Fq
from ws_rule import build, sc
def witness(t,T):
    """T: list of (x,y) points; t=(x,y). feasible xi=(a,b)>=0, a+b=1, a*dx+b*dy>=0 for all (dx,dy)=s-t. exact."""
    lo,hi=Fr(0),Fr(1)   # a in [lo,hi], b=1-a ; constraint a*dx+(1-a)*dy>=0 <=> a*(dx-dy) >= -dy
    for (x,y) in T:
        dx=x-t[0]; dy=y-t[1]; k=dx-dy
        if k>0: lo=max(lo,-dy/k)
        elif k<0: hi=min(hi,-dy/k)
        else:
            if dy<0: return False
    return lo<=hi
def moderate_ok(P,S,ell,delta=Fr(1,10**9)):
    e=Fr(float(np.exp(ell))); Sset=set(S); T=[P[q] for q in range(len(P)) if q not in Sset]
    for t in S:
        x,y=P[t]; gh=[(delta,y*e),(x*e,delta)]
        if not witness((x,y),T+gh): return False
    return True
def plain_ok(P,S):
    Sset=set(S); T=[P[q] for q in range(len(P)) if q not in Sset]
    return all(witness(P[t],T) for t in S)
if __name__=="__main__":
    kind="cp"; sw=build(kind); s=sc(sw); d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
    y=y_rational(s,[4],[Fr(2,100),Fr(8,100)],Fr(1,100),Fr(3,10))
    ells=[float(v) for v in os.environ.get("ELL","1.0,2.6,4.8,9.0").split(",")]
    for p,Q in list(zip(pats,Qs))[:int(os.environ.get("NP","3"))]:
        P=[(Fq(a),Fq(b)) for a,b in Q]; cert,msg=certify2(P,y)
        assert all(plain_ok(P,S) for S,m in cert)
        row=[(ell,sum(1 for S,m in cert if not moderate_ok(P,S,ell)),len(cert)) for ell in ells]
        print(p,"(ell, non-moderate sets, total):",row,flush=True)
