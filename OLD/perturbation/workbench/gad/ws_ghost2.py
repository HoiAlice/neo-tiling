"""Pointwise moderate check of the sets of an exact local certificate: S reachable against (C\S) u ghosts (NW/SE ghosts at log-distance ell)."""
import sys,os,time; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from fractions import Fraction as Fr
import planar
from ws_exact import y_rational
from ws_exact2 import certify2, Fq
from ws_ghost import augment
from ws_rule import build, sc
kind="cp"; sw=build(kind); s=sc(sw); d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
y=y_rational(s,[4],[Fr(2,100),Fr(8,100)],Fr(1,100),Fr(3,10))
ells=[float(v) for v in os.environ.get("ELL","1.0,2.6,4.8").split(",")]
for p,Q in list(zip(pats,Qs))[:int(os.environ.get("NP","4"))]:
    t0=time.time(); P=[(Fq(a),Fq(b)) for a,b in Q]; cert,msg=certify2(P,y)
    row=[]
    for ell in ells:
        Pg,gh=augment(Q,ell); Pa=Pg+gh
        bad=[i for i,(S,m) in enumerate(cert) if not planar.is_reachable(Pa,S,False)]
        row.append((ell,len(bad),len(cert)))
    print(p,"local exact cert sets:",len(cert),"| (ell, non-moderate sets, total):",row,"%.0fs"%(time.time()-t0),flush=True)
