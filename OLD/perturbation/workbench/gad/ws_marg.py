"""Does a log-margin m on all tight conflicts make local certificates moderate?  Polish with margin m (cost increase reported), exact certificate, moderate test at several ell."""
import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from fractions import Fraction as Fr
import cx2, cprime
from core import polish_margin, weakly_solvable
from ws_exact import y_rational
from ws_exact2 import certify2, Fq
from ws_ghost3 import moderate_ok, plain_ok
from ws_rule import build, sc
d=np.load("ws_ser.npz"); sw=cprime.build_c()[0]; A,Y,conf,ks=cx2.setup(sw)
i=3; sigma=[int(v) for v in d['sigma'][i]]; pat=tuple(d['pats'][i].tolist())
s=sc(build("cp")); y=y_rational(s,[4],[Fr(2,100),Fr(8,100)],Fr(1,100),Fr(3,10))
base=None
for m in (1e-8,1e-3,1e-2,5e-2,1e-1,2e-1):
    cm,u=polish_margin(A,conf,sigma,m); Q=np.exp(u)
    if base is None: base=cm
    ws=weakly_solvable(Q,np.array([float(v) for v in y]))
    row=[]
    if ws:
        P=[(Fq(a),Fq(b)) for a,b in Q]; cert,msg=certify2(P,y)
        if cert is not None:
            row=[(ell,sum(1 for S,_ in cert if not moderate_ok(P,S,ell)),len(cert)) for ell in (2.6,4.8,9.0,13.0)]
    print("pattern",pat,"margin m=%g"%m,"cost increase %.4f"%(cm-base),"| weakly solvable:",ws,"| (ell, non-moderate sets, total):",row,flush=True)
