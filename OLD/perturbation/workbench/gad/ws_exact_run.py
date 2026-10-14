import sys,os; sys.path.insert(0,".")
import numpy as np, time
from ws_exact import *
from ws_rule import build, sc
kind=sys.argv[1]; sw=build(kind); s=sc(sw); d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
if kind=="cp": kinks,slopes=[4],[Fr(2,100),Fr(7,100)]
else: kinks,slopes=[4],[Fr(2,100),Fr(7,100)]
y=y_rational(s,kinks,slopes,Fr(1,100),Fr(3,10))
res=[]
for p,Q in zip(pats,Qs):
    t=time.time(); ok=exact_check(Q,y); res.append(ok); print(kind,p,"exact certificate:",ok,"%.1fs"%(time.time()-t),flush=True)
print(kind,"ALL exact" if all(res) else "some failed",sum(res),"of",len(res))
