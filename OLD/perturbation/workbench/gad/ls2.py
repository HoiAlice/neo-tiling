from layout_search import *
from wedge import search as wsearch
import itertools, numpy as np
K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
sols=wsearch(4,K4,True)
print(len(sols),"type assignments")
cnt=0; best=[]
for combo in sols:
    ce=[e for e,c in enumerate(combo) if c[0]=="CE"]
    for nsel in itertools.product(range(3,16),repeat=len(ce)):
        ns=[0]*6
        for e,nn in zip(ce,nsel): ns[e]=nn
        x=solve(combo,ns,4)
        if x is None: continue
        L=x[8:]
        if (L>=8.9).all():
            cnt+=1
            bad=sum(0 if okP(l) else 1 for l in L)
            best.append((bad,combo,ns,np.round(L,2).tolist()))
print("integer-n layouts with all L>=8.9:",cnt)
best.sort(key=lambda b:b[0])
for b in best[:8]: print(b)
