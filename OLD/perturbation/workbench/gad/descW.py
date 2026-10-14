"""descW.py -- exhaustive-by-construction window enumeration for scheme2.  The witness layout W is a disjoint union of components realising every descriptor:
 K13 (K_{1,3}): stars of degree 3 at ranks 0,1,2 and degree-1 stars; P3: degree-2 stars at ranks 0,1; X (edges e0=(a,c), e1=(b,d) with bus order a<b<c<d): a crossing, arms with a crossing before the head (pad = minimum) ;
 D (two disjoint edges placed after other edges): arms without crossings with edge index >= 1 (pad = minimum + WC e: 'large').
Components are contiguous in the bus order, so tracks never span other components' buses; windows lie inside one component."""
import sys, itertools, collections, pickle
import numpy as np
import scheme, scheme2
from schemerun2 import surrogate_Y
from enum2 import window, anchors
from auditcores import canon
COMP={"K13":(4,[(0,1),(0,2),(0,3)]),"P3":(3,[(0,1),(1,2)]),"X":(4,[(0,2),(1,3)]),"D":(4,[(0,1),(2,3)])}
def witness():
    edges=[];off=0;comp={}
    order=["K13","P3","X","D","D"]      # second D pushes the edge index of the disjoint edges up
    for k,name in enumerate(order):
        n,E=COMP[name]
        for (i,j) in E: edges.append((off+i,off+j)); comp[len(edges)-1]=(k,name)
        off+=n
    return off,edges,order
def enumerate_types(R,RE,G,verbose=True):
    n,edges,order=witness(); L=scheme2.build(n,edges,RE,G,RW=int(R)); Y=surrogate_Y(L)
    # component of each vertex
    vcomp=[];off=0
    for k,name in enumerate(order):
        for _ in range(COMP[name][0]): vcomp.append(k)
    types={}
    anc=anchors(L)
    wins=[]
    for kind,a in anc:
        ids=window(L,a,R); order_ids=sorted(ids,key=lambda i:(L.sw[i][0],L.sw[i][1],L.sw[i][2]))
        sg=canon([L.sw[i] for i in ids],[(Y[2*i],Y[2*i+1]) for i in ids])
        # component of the anchor (via meta)
        m=L.meta[a]
        v=m.get('v',None)
        if v is None:
            e=m.get('e',None)
            if e is None: e=L.meta[a].get('e')
            v=L.edges[e][0]
        wins.append((kind,a,ids,order_ids,sg,vcomp[v]))
    ncomp=len(order)
    for k in range(ncomp):
        verts=[v for v in range(n) if vcomp[v]==k]
        for bits in itertools.product((0,1),repeat=len(verts)):
            vb=[0]*n
            for v,b in zip(verts,bits): vb[v]=b
            s,_=scheme.intended_bits(L,vb)
            for kind,a,ids,oi,sg,ck in wins:
                if ck!=k: continue
                d=types.setdefault((kind,sg),{}); bk=tuple(s[i] for i in oi)
                if bk not in d: d[bk]=(order[k],tuple(vb),a)
    if verbose: print("R",R,"(RE,G)",(RE,G),"witness switches",len(L.sw),"descriptor windows",len(wins),"types",len(types),dict(collections.Counter(k for (k,_) in types)),"(type,bits) pairs",sum(len(v) for v in types.values()),flush=True)
    return types,L
if __name__=="__main__":
    R=float(sys.argv[1]); RE=int(sys.argv[2]); G=int(sys.argv[3])
    types,L=enumerate_types(R,RE,G)
    pickle.dump({k:v for k,v in types.items()},open("descW_types_%d.pkl"%int(R),"wb"))
