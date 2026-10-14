import sys; sys.path.insert(0,".")
import numpy as np, time
from ws_exact import y_rational
from ws_exact2 import exact_ok
from ws_rule import build, sc
from fractions import Fraction as Fr
kind=sys.argv[1]; sw=build(kind); s=sc(sw); d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
y=y_rational(s,[4],[Fr(2,100),Fr(7,100)],Fr(1,100),Fr(3,10)); res=[]
for p,Q in zip(pats,Qs):
    t=time.time(); ok,msg=exact_ok(Q,y); res.append(ok); print(kind,p,"EXACT",ok,msg,"%.1fs"%(time.time()-t),flush=True)
print(kind,"exact certificates:",sum(res),"of",len(res))
