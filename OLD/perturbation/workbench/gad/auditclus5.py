import sys, itertools, collections
import numpy as np
import scheme
from schemerun import GRAPHS
from auditclus import window, anchors
from auditcores import canon
R=13.0
def keyof(L,Y,ids,sig):
    order=sorted(ids,key=lambda i:(L.sw[i][0],L.sw[i][1],L.sw[i][2]))
    return (canon([L.sw[i] for i in ids],[(Y[2*i],Y[2*i+1]) for i in ids]),tuple(sig[i] for i in order))
fails=[("K4",122,(0,0,0,0)),("K33",293,(0,0,0,0,0,0)),("K33",293,(0,0,0,1,0,0))]
failkeys=set()
for g,a,vb in fails:
    n,edges=GRAPHS[g]; L=scheme.build(n,edges); yt,yb,k=scheme.levels(L); Y=np.zeros(2*len(L.sw)); Y[0::2]=yt; Y[1::2]=yb
    ids=window(L,a,R); s,_=scheme.intended_bits(L,list(vb)); failkeys.add(keyof(L,Y,ids,s))
print("failing (window type, local bits) pairs:",len(failkeys))
for g in ("K3","K4","K33"):
    n,edges=GRAPHS[g]; L=scheme.build(n,edges); yt,yb,k=scheme.levels(L); Y=np.zeros(2*len(L.sw)); Y[0::2]=yt; Y[1::2]=yb
    best=max(sum(1 for (i,j) in edges if p[i]!=p[j]) for p in itertools.product((0,1),repeat=n))
    anc=anchors(L); wins=[(kind,a,window(L,a,R)) for kind,a in anc]
    for p in itertools.product((0,1),repeat=n):
        if sum(1 for (i,j) in edges if p[i]!=p[j])!=best: continue
        s,_=scheme.intended_bits(L,list(p))
        hits=[(kind,a) for kind,a,ids in wins if keyof(L,Y,ids,s) in failkeys]
        print(g,"max cut",p,"anchors whose window is a failing (type,bits):",hits)
