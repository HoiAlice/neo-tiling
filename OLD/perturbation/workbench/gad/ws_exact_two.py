import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, time
import ws_two as W
from ws_exact import y_rational
from ws_exact2 import exact_ok
from fractions import Fraction as Fr
y=y_rational(W.s,W.K,[Fr(2,100),Fr(62,100),Fr(122,100)],Fr(2,1000),Fr(3,10))
rng=np.random.default_rng(5); allp=[(i,j) for i in range(16) for j in range(16)]; sel=[allp[k] for k in rng.choice(256,int(os.environ.get("WS_N","6")),replace=False)]
ok=0
for ij in sel:
    t=time.time(); o,msg=exact_ok(W.Qcat(*ij),y); ok+=o; print("D",W.D,W.pats[ij[0]],W.pats[ij[1]],"exact",o,msg,"%.0fs"%(time.time()-t),flush=True)
print("D",W.D,"exact certificates",ok,"of",len(sel),flush=True)
