import sys, itertools, collections, random, pickle
import numpy as np
import scheme, scheme2
from schemerun2 import GRAPHS, surrogate_Y
from auditcores import canon
R=13.0
GR=dict(GRAPHS)
GR["P3"]=(3,[(0,1),(1,2)]); GR["Star13"]=(4,[(0,1),(0,2),(0,3)]); GR["C4"]=(4,[(0,1),(1,2),(2,3),(0,3)]); GR["C5"]=(5,[(0,1),(1,2),(2,3),(3,4),(0,4)])
GR["K4-e"]=(4,[(0,1),(0,2),(1,2),(1,3),(2,3)]); GR["Prism"]=(6,sorted(tuple(sorted(e)) for e in [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)]))
GR["Bull"]=(5,[(0,1),(0,2),(1,2),(1,3),(2,4)]); GR["Theta"]=(4,[(0,1),(0,2),(0,3),(1,2),(1,3)])
def anchors(L):
    A=[]
    for (v,k),c in L.star.items(): A.append(('star',c))
    for cr in L.crossings: A.append(('cross',cr['vidx']))
    for (e,u),a in L.arm.items():
        A.append(('corner',a['idx'][-1]))
        # plain anchors: every arm switch beyond the head that lies in the tail (irregular zone, pad, weak surroundings)
    for e,(a,b,u) in L.kink.items(): A.append(('kink',a))
    # arm tail anchors: every switch of the arm tail (after the head) at stride 1
    for (e,u),a in L.arm.items():
        ap=[p for p in L.plan[e]['arms'] if p['u']==u][0]
        for pos in range(ap['head']-2,len(a['idx'])): A.append(('tail',a['idx'][pos]))
    return A
def window(L,anchor,R):
    bx,by,d=L.sw[anchor]; cx,cy=float(bx+d/2),float(by+d/2); ids=[]
    for i,(x,y,dd) in enumerate(L.sw):
        x2,y2=float(x+dd/2),float(y+dd/2)
        if abs(x2-cx)<=R+(d+dd)/4 and abs(y2-cy)<=R+(d+dd)/4: ids.append(i)
    return ids
def patterns_for(n,edges,limit=300):
    allp=list(itertools.product((0,1),repeat=n))
    if len(allp)<=limit: return allp
    random.seed(5); pats=random.sample(allp,limit)
    best=max(sum(1 for (i,j) in edges if p[i]!=p[j]) for p in allp[:2048]) if n<=11 else None
    return pats
def collect(graphs,RE=6,G=16,verbose=True):
    types={}   # (kind,sig) -> {bitskey: (graph,pattern,anchor)}
    growth=[]
    for g in graphs:
        n,edges=GR[g]; L=scheme2.build(n,edges,RE,G,RW=int(R)); Y=surrogate_Y(L)
        anc=anchors(L); wins=[(k,a,window(L,a,R)) for k,a in anc]
        sigs=[]
        for kind,a,ids in wins:
            order=sorted(ids,key=lambda i:(L.sw[i][0],L.sw[i][1],L.sw[i][2]))
            sg=canon([L.sw[i] for i in ids],[(Y[2*i],Y[2*i+1]) for i in ids]); sigs.append((kind,a,ids,order,sg))
        for p in patterns_for(n,edges):
            s,_=scheme.intended_bits(L,list(p))
            for kind,a,ids,order,sg in sigs:
                key=(kind,sg); bk=tuple(s[i] for i in order)
                d=types.setdefault(key,{})
                if bk not in d: d[bk]=(g,p,a)
        growth.append((g,len(types),collections.Counter(k for (k,_) in types)))
        if verbose: print(g,"switches",len(L.sw),"cumulative window types",len(types),dict(growth[-1][2]),flush=True)
    return types,growth
if __name__=="__main__":
    graphs=sys.argv[1].split(",")
    types,growth=collect(graphs)
    pickle.dump({k:v for k,v in types.items()},open("enum2_types.pkl","wb"))
    print("TOTAL types",len(types),"(type,bits) pairs",sum(len(v) for v in types.values()))
