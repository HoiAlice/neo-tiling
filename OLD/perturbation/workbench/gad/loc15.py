import numpy as np, cx2
from loc8 import build_inst
sw=build_inst(3.75); A,Y,conf,ks=cx2.setup(sw); T=len(A)
P1=[[1,2,3,4,5,6,7,18,19,20,21,22,23],[0,9],[10],[11,12],[13,14],[8],[15],[16,17],[24]]
P2=[[2,3,4,5,6,19,20,21,22],[0,1],[9,10,11,12,13],[14],[7,8],[15,16,17,18],[23,24]]
def blk(P): 
    m={}
    for k,b in enumerate(P):
        for s in b: m[s]=k
    return m
m1,m2=blk(P1),blk(P2)
full=[(t,s) for t in range(T) for s in range(T) if Y[t]>Y[s]]
for thr in (1.0,1.2,1.3):
    bad=[]
    for t,s in full:
        sep=max(A[s,i]-A[t,i] for i in range(2))
        if sep<thr:
            a,b=t//2,s//2
            if not ((m1[a]==m1[b]) or (m2[a]==m2[b])): bad.append((a,b,round(sep,3)))
    print("sep<",thr,"conflicts not inside a common block:",len(bad),sorted(set(bad))[:12])
