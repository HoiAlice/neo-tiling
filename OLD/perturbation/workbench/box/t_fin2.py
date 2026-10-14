"""critical / collinear / zero-width families with exact closed-box construction"""
import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
from fractions import Fraction as F
from exactbox import *
import numpy as np
res=[];rng=np.random.default_rng(5)
# 1. triangle at critical a, +-1e-9 ; random widths; with construction at the critical one
ok=True
for w in [F(0),F(1,3),F(2),F(7,5)]:
  for wt in [F(0),F(1,5),F(3)]:
    L=[(F(1),F(4)),(F(4),F(1)),(F(0),F(0))];U=[(F(1)+w,F(4)+w),(F(4)+w,F(1)+w),(F(0),F(0))];y=[F(1),F(1),F(5)]
    a=F(5,2)+w
    out=[]
    for da in [F(0),F(1,10**9),-F(1,10**9)]:
        L[2]=(a+da,a+da);U[2]=(a+da+wt,)*2
        d=decide_closed(L,U,y);out.append(d)
        if d:
            Q=construct_closed(L,U,y);good=all(L[t][i]<=Q[t][i]<=U[t][i] for t in range(3) for i in range(2)) and certify_Q(Q,y)
            ok&=good
    # expected: critical True; +1e-9 True iff wt>0 (box lets L_t.. no: L_t above line but Q must be >= L_t) -> False; -1e-9 True
    exp=[True,False,True]
    res.append(out==exp)
    if out!=exp: print("unexpected",w,wt,out)
print("critical triangle families (closed box, exact):",sum(res),"of",len(res),"as expected; constructions certified:",ok)
# 2. collinear corners: points on a common line / aligned coordinates, all boxes zero-width or unit
st=[0,0]
for it in range(200):
    T=int(rng.integers(3,6));k=int(rng.integers(0,3))
    base=[(F(i+1),F(6-i)) for i in range(T)]            # all on x+y=7 (collinear)
    L=[(b[0]+F(int(rng.integers(0,2)))*(k>0),b[1]) for b in base];U=[(L[t][0]+F(int(rng.integers(0,2))),L[t][1]+F(int(rng.integers(0,2)))) for t in range(T)]
    y=[F(int(v)) for v in rng.integers(0,4,T)]
    a=decide_closed(L,U,y);b=decide(L,U,y);st[0]+=(a==b)
    if a:
        Q=construct_closed(L,U,y);st[1]+= all(L[t][i]<=Q[t][i]<=U[t][i] for t in range(T) for i in range(2)) and certify_Q(Q,y)
    else: st[1]+=1
print("collinear/aligned corners: closed-LP == delta-LP in",st[0],"of 200; constructions certified (or infeasible)",st[1])
