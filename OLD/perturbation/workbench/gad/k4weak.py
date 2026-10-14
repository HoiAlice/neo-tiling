import sys, itertools, numpy as np, time, cx2
import k4glue
from k4glue import *
from snapw import snap
from core import weakly_solvable
from ysolve import find_y
def glue_Q(pat,margin_shift=0.0):
    A,conf,ks=G["A"],G["conf"],G["ks"]
    sig,strong,weak=intended(G["sol"],G["inst"],G["chains"],G["by_edge"],pat)
    own={k:sig[i] for i,k in enumerate(ks)}; assign=dict(own); tol=1e-7
    for it in range(40):
        edges=[[],[]]
        for k,c in assign.items(): edges[c].append(conf[k])
        c0,u0=iso_cost(A[:,0],edges[0]); c1,u1=iso_cost(A[:,1],edges[1])
        u=np.column_stack([u0,u1]); viol=[]
        for k,(t,s) in enumerate(conf):
            if k in assign: continue
            d0=u[t,0]-u[s,0]; d1=u[t,1]-u[s,1]
            if d0>tol and d1>tol: viol.append((k,0 if d0<=d1 else 1,min(d0,d1)))
        if not viol: break
        viol.sort(key=lambda x:-x[2])
        for k,c,_ in viol[:max(1,len(viol)//3+1)]: assign[k]=c
    return u,c0+c1
if __name__=="__main__":
    init()
    pats=[p for p in itertools.product((0,1),repeat=4) if sum(p)==2]
    Qs=[]
    for p in pats:
        u,c=glue_Q(p); Us=snap(u,1e-5); Qs.append(np.exp(Us)); print(p,"cost",round(c,5),flush=True)
    Y=G["Y"]; t0=time.time()
    y=find_y(Qs,Y,1e-6,100); print("joint y feasible",y is not None,"time",round(time.time()-t0),flush=True)
    if y is not None:
        print("max/min",y.max()/y.min(),flush=True)
        print("weak at found y",[weakly_solvable(Q,y) for Q in Qs],flush=True)
    print("weak at generator y",[weakly_solvable(Q,Y) for Q in Qs],flush=True)
