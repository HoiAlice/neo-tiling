import sys,os; sys.path.insert(0,".")
import numpy as np, time
from ws_exact import y_rational
from ws_exact2 import exact_ok
from ws_rule import build, sc
from fractions import Fraction as Fr
kind=sys.argv[1]; rule=sys.argv[2]   # base | final
sw=build(kind); s=sc(sw); d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
if rule=="base": y=y_rational(s,[4],[Fr(2,100),Fr(7,100)],Fr(1,100),Fr(3,10))
else: y=y_rational(s,[4],[Fr(2,100),Fr(62,100)],Fr(2,1000),Fr(3,10))
res=[]
for p,Q in zip(pats,Qs):
    ok,msg=exact_ok(Q,y); res.append(ok)
    if not ok: print(kind,rule,p,"FAILED",msg,flush=True)
print(kind,rule,"exact certificates:",sum(res),"of",len(res),flush=True)
