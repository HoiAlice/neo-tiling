import sys, pickle, numpy as np, cx2, time
from layout import *
from core import solve_dom
def get():
    key,rs,tr,sol,inst=pickle.load(open("lay_k4_best.pkl","rb"))
    lv=levels(inst["sw"]); return sol,inst,lv
def run(pat,tl,marg):
    sol,inst,lv=get()
    A,Y,conf,ks=cx2.setup(lv)
    idx=[inst["vidx"][v] for v in range(4)]
    fixed=dict(zip([ks[i] for i in idx],pat))
    own=set(ks); nfree=0
    for k,(t,s) in enumerate(conf):
        if k in fixed or k in own: continue
        m0=A[s,0]-A[t,0]; m1=A[s,1]-A[t,1]
        if max(m0,m1)>=marg: fixed[k]=0 if m0>=m1 else 1
        else: nfree+=1
    t0=time.time()
    r=solve_dom(A,Y,fixed=fixed,conflicts=conf,time_limit=tl)
    return nfree,r,time.time()-t0
if __name__=="__main__":
    pat=tuple(int(c) for c in sys.argv[1]); tl=int(sys.argv[2]); marg=float(sys.argv[3])
    nfree,r,dt=run(pat,tl,marg)
    print(pat,"free conflicts",nfree,"milp lb",round(r[0],5),"exact",round(r[2],6),"time",round(dt),flush=True)
