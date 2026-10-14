"""Moderate-witness local certificates via ghost points.  For a cluster C (prices Q, values y) and log-radius ell, add for every point t
 a NW ghost (delta, y_t*e^ell) and a SE ghost (x_t*e^ell, delta) with y=0.  A set S in C that is weakly reachable against (C\S) u ghosts has, for every t in S,
a witness xi with xi_hat2/xi_hat1 in [1/K,K] (K=e^ell-1) w.r.t. the natural direction at t, hence against ALL far-field points (far-field lemma)."""
import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from fractions import Fraction as Fr
import planar
from ws_exact2 import certify2, check, Fq
def augment(Q,ell,delta=1e-9):
    P=[(Fq(a),Fq(b)) for a,b in Q]; e=Fr(float(np.exp(ell))); d=Fr(delta)
    gh=[]
    for (x,y) in P:
        gh.append((d,y*e)); gh.append((x*e,d))
    return P,gh
def ghost_cert(Q,y,ell):
    P,gh=augment(Q,ell); Pa=P+gh; ya=list(y)+[Fr(0)]*len(gh)
    cert,msg=certify2(Pa,ya)
    return cert,msg,Pa,ya
if __name__=="__main__":
    from ws_exact import y_rational
    from ws_rule import build, sc
    kind="cp"; sw=build(kind); s=sc(sw); d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
    y=y_rational(s,[4],[Fr(2,100),Fr(8,100)],Fr(1,100),Fr(3,10))
    for ell in [float(v) for v in os.environ.get("ELL","1.0,2.6,4.8").split(",")]:
        ok=0
        for p,Q in list(zip(pats,Qs))[:int(os.environ.get('NP','16'))]:
            cert,msg,Pa,ya=ghost_cert(Q,y,ell)
            good=cert is not None and check(Pa,ya,cert); ok+=good
            if not good: print("  ell",ell,p,"FAIL",msg,flush=True)
        print("ell",ell,"K=%.1f"%(np.exp(ell)-1),"moderate local certificates exact:",ok,"of",min(len(Qs),int(os.environ.get('NP','16'))),flush=True)
