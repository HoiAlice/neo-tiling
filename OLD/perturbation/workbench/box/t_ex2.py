import sys,time
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as F
from exactbox import *
# (a) tight triangle family: r=(1,4)+, s=(4,1)+, t=(a,a); exact critical a = 5/2 + u
res=[]
for u in [F(0),F(1,3),F(1,2),F(2)]:
    for mode in ["fixed","box"]:
        w=F(0) if mode=="fixed" else u
        L=[(F(1),F(4)),(F(4),F(1)),None];U=[(F(1)+w,F(4)+w),(F(4)+w,F(1)+w),None]
        y=[F(1),F(1),F(5)]
        acrit=F(5,2)+w     # L_t=(a,a) on line x+y=5+2w through U_r,U_s
        out=[]
        for a in [acrit, acrit+F(1,10**6), acrit-F(1,10**6)]:
            L[2]=(a,a);U[2]=(a+(F(1,5) if mode=="box" else 0),)*2
            out.append(decide(L,U,y))
        res.append((mode,u,out)); print(mode,"w",w,"at critical / +1e-6 / -1e-6 :",out)
ok=all(o==[True,False,True] for _,_,o in res); print("tight triangle all as expected:",ok)
# (b) planted degenerate boxes: Q, y in cone, boxes with zero-width coords
rng=np.random.default_rng(3);N=0;good=0;cons=0;consok=0;t0=time.time()
for it in range(40):
    T=int(rng.integers(3,5));Q=[(F(int(a)),F(int(b))) for a,b in rng.integers(1,6,(T,2))]
    y=[F(0)]*T;cnt=0
    for _ in range(30):
        S=[t for t in range(T) if rng.random()<0.5]
        if S and planar.is_reachable(Q,S,strict=False): 
            c=F(int(rng.integers(1,4)));cnt+=1
            for t in S: y[t]+=c
    if cnt==0: continue
    L=[];U=[]
    for t in range(T):
        wd=[F(int(rng.integers(0,3)))*F(int(rng.integers(0,2))) for _ in range(2)]   # many zeros
        sh=[F(int(rng.integers(0,int(wd[i])+1))) if wd[i]>0 else F(0) for i in range(2)]
        L.append(tuple(max(F(1,2),Q[t][i]-sh[i]) for i in range(2)));U.append(tuple(L[t][i]+wd[i] if L[t][i]+wd[i]>=Q[t][i] else Q[t][i] for i in range(2)))
    N+=1; ok=decide(L,U,y); good+=ok
    if not ok: print("PLANTED BUT LP FALSE",L,U,y)
    else:
        d=delta_bound(L,U);Qc=construct(L,U,y,2*d)
        inE=all(L[t][i]-2*d<=Qc[t][i]<=U[t][i]+2*d for t in range(T) for i in range(2))
        cons+=1;consok+= inE and certify_Q(Qc,y)
print("planted degenerate boxes: LP true in",good,"of",N,"; constructed rational Q in E_2delta, exact certificate:",consok,"of",cons,"time %.0fs"%(time.time()-t0))
