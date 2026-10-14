import numpy as np, sys, itertools
sys.path.insert(0,'pc')
from land import lp_cost
seed=int(sys.argv[1]); rng=np.random.default_rng(seed)
G=np.linspace(0.04,0.96,13)
def landscape1(P,hi,nl):
    return np.array([lp_cost(P,[hi],list(range(nl)),{hi:g}) for g in G])
def split(c):
    lm=[i for i in range(1,len(G)-1) if c[i]<c[i-1]-1e-6 and c[i]<=c[i+1]+1e-9]
    if len(lm)<2: return None
    a,b=lm[0],lm[-1]; cut=a+int(np.argmax(c[a:b+1]))
    return list(range(0,cut+1)),list(range(cut+1,len(G)))
neg=0;pos=0;zero=0;tot=0
for trial in range(int(sys.argv[2])):
    nl=rng.integers(3,6)
    xs=np.sort(rng.uniform(0.5,6,nl)); ys=np.sort(rng.uniform(0.5,6,nl))[::-1]
    L=np.c_[xs,ys]
    hs=[np.array([rng.uniform(xs.min(),xs.max()), rng.uniform(ys.min(),ys.max())]) for _ in range(2)]
    P=np.vstack([L]+hs); h1,h2=nl,nl+1
    # per-heavy classes from single-heavy landscapes (other heavy removed)
    cls=[]
    ok=True
    for hh in (h1,h2):
        idx=list(range(nl))+[hh]
        Pp=P[idx]; c=landscape1(Pp,nl,nl)
        s=split(c)
        if s is None: ok=False;break
        cls.append(s)
    if not ok: continue
    tot+=1
    F={}
    for a in range(2):
        for b in range(2):
            best=np.inf
            for i in cls[0][a]:
                for j in cls[1][b]:
                    v=lp_cost(P,[h1,h2],list(range(nl)),{h1:G[i],h2:G[j]})
                    best=min(best,v)
            F[a,b]=best
    d=F[0,0]+F[1,1]-F[0,1]-F[1,0]
    if d<-1e-4: neg+=1; print("FERRO",trial,round(d,4),{k:round(v,3) for k,v in F.items()},np.round(P,2).tolist())
    elif d>1e-4: pos+=1; print("POS",trial,round(d,4),{k:round(v,3) for k,v in F.items()},np.round(P,2).tolist())
    else: zero+=1
print("seed",seed,"tot",tot,"ferro(d>0 means anti)",pos,"neg",neg,"zero",zero)
