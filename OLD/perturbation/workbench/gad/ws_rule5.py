import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, cx2
from ws_rule import *
from ws_rule4 import y_pw
from core import weakly_solvable
def nm(q): return "s%d%s"%(q//2,"t" if q%2==0 else "b")
for kind in ("cp","k3"):
    sw=build(kind); A,Y,conf,ks=cx2.setup(sw); S=set(conf); d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
    for (c1,c2,ss) in [(0.02,0.08,4),(0.03,0.08,4),(0.02,0.07,4),(0.02,0.06,4)]:
        y=y_pw(sw,c1,c2,ss); A2,c=setup_with(sw,y); R=set(c)
        extra=[(nm(a),nm(b)) for a,b in R-S]; miss=[(nm(a),nm(b)) for a,b in S-R]
        ok=[bool(weakly_solvable(Q,y)) for Q in Qs]
        # extra conflicts satisfied at all Q?
        sat=all(min(Q[a,0]-Q[b,0],Q[a,1]-Q[b,1])<=1e-9 for a,b in R-S for Q in Qs)
        print(kind,(c1,c2,ss),"ratio %.2f"%(y.max()/y.min()),"extra",extra,"extra satisfied at all Q:",sat,"missing",miss,"weak:","ALL" if all(ok) else "fail %s"%[tuple(p) for p,o in zip(pats,ok) if not o][:4],flush=True)
