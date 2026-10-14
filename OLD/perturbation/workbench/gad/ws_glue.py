"""Gluing construction on two clusters (copy 1 SW, copy 2 NE): local exact certificates + lifting S -> S u Low_k; exact verification of every lifted set and of the sum."""
import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar, time
from fractions import Fraction as Fr
import ws_two as W
from ws_exact import y_rational
from ws_exact2 import certify2, Fq
from ws_exact3 import certify3
CONTEXT=bool(int(os.environ.get('WS_CTX','1')))
def glue(Q,y,kappa=Fr(0),verbose=True):
    n1=2*W.n1; N=len(y); yp=[v-(1-kappa) for v in y]
    B=[list(range(0,n1)),list(range(n1,N))]
    P=[(Fq(a),Fq(b)) for a,b in Q]
    fam=[]   # (global set, mass)
    # top cluster first
    c=Fr(0); 
    for k in (1,0):
        idx=B[k]; nu=[yp[p]-c for p in idx]
        if min(nu)<0: return False,"level condition fails at cluster %d: min nu=%s"%(k,float(min(nu)))
        ctx=[p for kk in range(k+1,2) for p in B[kk]] if CONTEXT else []
        cert,msg,_=certify3([P[p] for p in idx+ctx],nu+[Fr(0)]*len(ctx))
        if cert is None: return False,"local certificate fails at cluster %d: %s"%(k,msg)
        M=sum(m for _,m in cert)
        low=frozenset(range(0,n1)) if k==1 else frozenset()
        for S,m in cert: fam.append((frozenset(idx[q] for q in S)|low,m))
        c+=M
    # verification of the lifted family (exact), + base 1_all
    tot=[1-kappa]*N
    for S,m in fam:
        if not planar.is_reachable(P,S,False): return False,"lifted set not reachable (size %d, mass %s)"%(len(S),float(m))
        for q in S: tot[q]+=m
    return tot==list(y),"sum matches" if tot==list(y) else "sum mismatch"
if __name__=="__main__":
    y=y_rational(W.s,W.K,[Fr(2,100),Fr(62,100),Fr(122,100)],Fr(2,1000),Fr(3,10))
    rng=np.random.default_rng(11); allp=[(i,j) for i in range(16) for j in range(16)]; sel=[allp[k] for k in rng.choice(256,int(os.environ.get("WS_N","4")),replace=False)]
    for ij in sel:
        t=time.time(); ok,msg=glue(W.Qcat(*ij),y,Fr(os.environ.get('WS_KAPPA','0.01'))); print("shift",W.DX,W.DY,W.pats[ij[0]],W.pats[ij[1]],"GLUING",ok,msg,"%.0fs"%(time.time()-t),flush=True)
