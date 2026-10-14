import sys, itertools, numpy as np, random
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
from iso_scipy import iso_cost
def F(a,sigma,conf):
    e=[[],[]]
    for (t,s),i in zip(conf,sigma): e[i].append((t,s))
    return iso_cost(a[0],e[0])[0]+iso_cost(a[1],e[1])[0]
rng=np.random.default_rng(int(sys.argv[1]))
T=int(sys.argv[2]); trials=int(sys.argv[3])
viol=0; tot=0; examples=[]
for tr in range(trials):
    P=np.exp(rng.uniform(0,1.5,size=(T,2)))
    y=rng.permutation(T).astype(float)+1
    a=[np.log(P[:,0]),np.log(P[:,1])]
    conf=[(t,s) for t in range(T) for s in range(T) if y[t]>y[s] and P[t,0]>P[s,0] and P[t,1]>P[s,1]]
    c=len(conf)
    if c<2 or c>9: continue
    cache={}
    def G(s):
        if s not in cache: cache[s]=F(a,s,conf)
        return cache[s]
    worst=0
    for e1 in range(c):
        for e2 in range(e1+1,c):
            for rest in itertools.product((0,1),repeat=c-2):
                def mk(b1,b2):
                    s=list(rest); s.insert(e1,b1); s.insert(e2,b2); return tuple(s)
                d=G(mk(1,0))+G(mk(0,1))-G(mk(0,0))-G(mk(1,1))
                tot+=1
                if d<-1e-6:
                    viol+=1; worst=min(worst,d)
    if worst<0: examples.append((tr,c,worst))
print("T",T,"pairs tested",tot,"submodularity violations",viol)
print(examples[:5])
