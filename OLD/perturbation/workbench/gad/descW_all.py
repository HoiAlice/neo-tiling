import sys, itertools, collections, pickle
import numpy as np
import scheme, scheme2, descW
from schemerun2 import surrogate_Y
from enum2 import window
from auditcores import canon
R=float(sys.argv[1]); RE=int(sys.argv[2]); G=int(sys.argv[3])
n,edges,order=descW.witness(); L=scheme2.build(n,edges,RE,G,RW=int(R)); Y=surrogate_Y(L)
vcomp=[]
for k,name in enumerate(order): vcomp+=[k]*descW.COMP[name][0]
def vof(a):
    m=L.meta[a]; v=m.get('v')
    if v is None: v=L.edges[m['e']][0]
    return v
wins=[]
for a in range(len(L.sw)):
    ids=window(L,a,R); oi=sorted(ids,key=lambda i:(L.sw[i][0],L.sw[i][1],L.sw[i][2]))
    sg=canon([L.sw[i] for i in ids],[(Y[2*i],Y[2*i+1]) for i in ids]); wins.append((L.meta[a]['kind'],a,ids,oi,sg,vcomp[vof(a)]))
types={}
for k in range(len(order)):
    verts=[v for v in range(n) if vcomp[v]==k]
    for bits in itertools.product((0,1),repeat=len(verts)):
        vb=[0]*n
        for v,b in zip(verts,bits): vb[v]=b
        s,_=scheme.intended_bits(L,vb)
        for kind,a,ids,oi,sg,ck in wins:
            if ck!=k: continue
            d=types.setdefault(sg,{}); bk=tuple(s[i] for i in oi)
            if bk not in d: d[bk]=(order[k],tuple(vb),a)
print("R",R,"every-switch anchors: windows",len(wins),"distinct window types",len(types),"(type,bits) pairs",sum(len(v) for v in types.values()))
pickle.dump(types,open("descW_all_%d.pkl"%int(R),"wb"))
