"""Two-layer decomposition: explicit gap layer Gamma (sets {q: x_q<x_t} u {top_t} or y-type, mass g_t) + remainder r = y - b - Gamma. Test r>=0 and weak solvability of r."""
import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as Fr
from ws_exact import y_rational
from ws_exact2 import Fq
from ws_rule import build, sc
from core import weakly_solvable
kind="cp"; sw=build(kind); s=sc(sw); n=len(sw)
d=np.load("ws_snap_cp.npz"); Qs=list(d['Qs']); pats=d['pats'].tolist()
gap=Fr(1,100); y=y_rational(s,[4],[Fr(2,100),Fr(8,100)],gap,Fr(3,10)); yf=np.array([float(v) for v in y]); g_t=[yf[2*i]-yf[2*i+1] for i in range(n)]
ok_all=0
for p,Q in zip(pats,Qs):
    P=[(Fq(a),Fq(b)) for a,b in Q]
    G=np.zeros(2*n); valid=True; types=[]
    for i in range(n):
        t=2*i; b=2*i+1; dx=abs(Q[t,0]-Q[b,0]); dy=abs(Q[t,1]-Q[b,1]); xt=dx<dy   # x-type if x coordinates agree
        types.append("x" if xt else "y")
        if xt: S={q for q in range(2*n) if Q[q,0]<Q[t,0]-1e-12}|{t}
        else: S={q for q in range(2*n) if Q[q,1]<Q[t,1]-1e-12}|{t}
        if b in S: valid=False
        for q in S: G[q]+=g_t[i]
    # reachable check of each gap set (exact)
    rc=True
    for i in range(n):
        t=2*i; xt=types[i]=="x"
        S=[q for q in range(2*n) if (P[q][0]<P[t][0] if xt else P[q][1]<P[t][1])]+[t]
        if not planar.is_reachable(P,S,False): rc=False; break
    bmin=min(yf[q]-G[q] for q in range(2*n)); b0=max(0.0,bmin-1e-9)
    r=yf-b0-G
    print(p,"x-type switches",types.count("x"),"y-type",types.count("y"),"| gap sets reachable:",rc,"| min(y-G)=%.4f"%bmin,"r>=0:",bool(r.min()>=-1e-12),"| r solvable:",bool(weakly_solvable(Q,np.maximum(r,0))),"| r top/bottom spread max %.2e"%max(abs(r[2*i]-r[2*i+1]) for i in range(n)),flush=True)
