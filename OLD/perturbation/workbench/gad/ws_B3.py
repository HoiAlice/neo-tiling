"""Gap-scaling rule: from the hand-set levels, gaps equal to one unit stay, larger gaps are multiplied by f. Test on all snapped patterns."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from core import weakly_solvable
kind=sys.argv[1]; d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); Y=d['Y']
lv=sorted(set(np.round(Y,9)),reverse=True); unit=min(a-b for a,b in zip(lv,lv[1:]))
for f in (5,6,9,12):
    z=[0.0]
    for a,b in zip(lv,lv[1:]):
        g=(a-b)/unit; z.append(z[-1]+(g if abs(g-1)<1e-6 else f*g))
    z=np.array(z); z=(z.max()-z)/(z.max()-z.min()); e=np.zeros(len(Y))
    for k,l in enumerate(lv):
        for i in range(len(Y)):
            if round(Y[i],9)==l: e[i]=z[k]
    ok=[bool(weakly_solvable(Q,1+0.1*e)) for Q in Qs]
    print(kind,"f",f,"passes",sum(ok),"of",len(ok),flush=True)
