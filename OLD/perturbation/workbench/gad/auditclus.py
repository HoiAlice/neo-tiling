import sys, collections, itertools, pickle
import numpy as np
import scheme, audit, qstar
from schemerun import GRAPHS
from auditcores import canon
def anchors(L):
    """anchor switches: star centres, crossing V centres, corners (u0 of every arm = last arm switch and V'_0 / V_0), kink pair (left switch)"""
    A=[]
    for (v,k),c in L.star.items(): A.append(('star',c))
    for cr in L.crossings: A.append(('cross',cr['vidx']))
    for (e,u),a in L.arm.items(): A.append(('corner',a['idx'][-1]))
    for e,(a,b,u) in L.kink.items(): A.append(('kink',a))
    return A
def window(L,anchor,R):
    bx,by,d=L.sw[anchor]; cx,cy=float(bx+d/2),float(by+d/2)
    ids=[]
    for i,(x,y,dd) in enumerate(L.sw):
        x2,y2=float(x+dd/2),float(y+dd/2)
        if abs(x2-cx)<=R+(d+dd)/4 and abs(y2-cy)<=R+(d+dd)/4: ids.append(i)
    return ids
def enum(R,graphs=("K3","K4","K33"),verbose=True):
    types=collections.defaultdict(list)
    for g in graphs:
        n,edges=GRAPHS[g]; L=scheme.build(n,edges)
        yt,yb,k=scheme.levels(L); Y=np.zeros(2*len(L.sw)); Y[0::2]=yt; Y[1::2]=yb
        for kind,a in anchors(L):
            ids=window(L,a,R)
            sig=canon([L.sw[i] for i in ids],[(Y[2*i],Y[2*i+1]) for i in ids])
            types[(kind,sig)].append((g,a,len(ids)))
    return types
if __name__=="__main__":
    R=float(sys.argv[1])
    t=enum(R)
    bykind=collections.defaultdict(list)
    for (kind,sig),occ in t.items(): bykind[kind].append((len(sig[0]),len(occ)))
    print("R",R)
    for kind,v in bykind.items(): print(kind,"distinct window types",len(v),"sizes (min,max)",min(x[0] for x in v),max(x[0] for x in v),"occurrences",sum(x[1] for x in v))
