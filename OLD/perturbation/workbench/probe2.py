import sys, itertools, numpy as np
sys.path.insert(0,'/Users/olegoleg/Code/neo-tiling/perturbation/experiments')
from iso_scipy import iso_cost
rng=np.random.default_rng(5)
def Fall(P,y):
    T=len(P); a=[np.log(P[:,0]),np.log(P[:,1])]
    conf=[(t,s) for t in range(T) for s in range(T) if y[t]>y[s]]
    C=len(conf); F={}
    for sig in itertools.product((0,1),repeat=C):
        e=[[],[]]
        for (t,s),i in zip(conf,sig): e[i].append((t,s))
        F[sig]=iso_cost(a[0],e[0])[0]+iso_cost(a[1],e[1])[0]
    return conf,F
def check(F):
    keys=list(F); sub=sup=0; n=0
    C=len(keys[0])
    for _ in range(4000):
        a=keys[rng.integers(len(keys))]; b=keys[rng.integers(len(keys))]
        m=tuple(min(u,v) for u,v in zip(a,b)); M=tuple(max(u,v) for u,v in zip(a,b))
        d=F[m]+F[M]-F[a]-F[b]
        if d>1e-6: sup+=1
        if d<-1e-6: sub+=1
        n+=1
    return sub,sup,n
for it in range(6):
    T=4
    P=np.exp(rng.normal(0,0.6,(T,2))); y=np.array([1,2,3,4.])
    conf,F=Fall(P,y)
    print(it,len(conf),check(F), min(F.values()))
