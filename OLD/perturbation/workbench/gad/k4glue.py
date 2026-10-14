import sys, itertools, numpy as np, cx2, time
from multiprocessing import Pool
from k4ub import *
from iso_scipy import iso_cost
K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
G={}
def init():
    sol,inst,lv=get(); A,Y,conf,ks=cx2.setup(lv)
    chains,by_edge=build_chains(sol,inst); G.update(sol=sol,inst=inst,A=A,Y=Y,conf=conf,ks=ks,chains=chains,by_edge=by_edge)
def glue(pat,tol=1e-7,maxit=40):
    A,conf,ks=G["A"],G["conf"],G["ks"]
    sig,strong,weak=intended(G["sol"],G["inst"],G["chains"],G["by_edge"],pat)
    own={k:sig[i] for i,k in enumerate(ks)}
    assign=dict(own)           # conflict index -> coordinate (only constrained ones)
    for it in range(maxit):
        edges=[[],[]]
        for k,c in assign.items(): edges[c].append(conf[k])
        c0,u0=iso_cost(A[:,0],edges[0]); c1,u1=iso_cost(A[:,1],edges[1])
        u=np.column_stack([u0,u1]); viol=[]
        for k,(t,s) in enumerate(conf):
            if k in assign: continue
            d0=u[t,0]-u[s,0]; d1=u[t,1]-u[s,1]
            if d0>tol and d1>tol: viol.append((k,0 if d0<=d1 else 1,min(d0,d1)))
        if not viol: break
        # add the worst few violations
        viol.sort(key=lambda x:-x[2])
        for k,c,_ in viol[:max(1,len(viol)//3+1)]: assign[k]=c
    # exact recheck of all conflicts
    nviol=sum(1 for (t,s) in conf if u[t,0]-u[s,0]>tol and u[t,1]-u[s,1]>tol)
    return pat,c0+c1,nviol,it+1,strong,weak
if __name__=="__main__":
    pats=list(itertools.product((0,1),repeat=4))
    t0=time.time()
    with Pool(5,initializer=init) as p:
        for r in p.imap_unordered(glue,pats):
            pat,c,nv,it,st,wk=r; unc=sum(1 for (u,v) in K4 if pat[u]==pat[v])
            print(pat,"uncut",unc,"cost",round(c,5),"violations",nv,"iters",it,"kinks S/W",st,wk,"t",round(time.time()-t0),flush=True)
