import sys, itertools, collections, pickle, time
import numpy as np
import scheme2, audit, auditcert, auditcores
from schemerun2 import GRAPHS, surrogate_Y
from audit import tilings, lemmaC
RE,G=int(sys.argv[1]),int(sys.argv[2])
allsig=collections.Counter()
for g in ("K3","K4","K33","Q3","Petersen"):
    n,edges=GRAPHS[g]; t0=time.time(); L=scheme2.build(n,edges,RE,G); T=tilings(L)
    print(g,"switches",len(L.sw),"stretches",len(T['stretches']),"plain blocks P1",len(T['P1plain']),"P2",len(T['P2plain']),"star cores",len(T['star_cores']),"crossing cores",len(T['cross_cores']),flush=True)
    worst=lemmaC(L,T,g)
    Y=surrogate_Y(L); c=auditcert.plain_blocks(L,T,Y)
    for (tag,sig),cnt in c.items(): allsig[sig]+=cnt
    sb=auditcores.scheme_blocks(L,Y); lib=auditcores.library()
    for kind,lst in sb.items():
        cnt=collections.Counter(lst); print("   ",kind,"blocks",len(lst),"distinct",len(cnt),"equal to library:",sum(v for s,v in cnt.items() if s==lib[kind]),flush=True)
    rel=T['rel']; core_of=T['core_of']
    bad=[1 for (a,b),v in rel.items() if v['owner'][0]=='edge' and not (core_of.get(a) is not None and core_of.get(b) is not None) and v['c1']+v['c2']<2]
    print("   edge-owned relations with avg credit < J_e:",len(bad),"| time",round(time.time()-t0),"s",flush=True)
print("DISTINCT plain block types over all graphs:",len(allsig),"sizes",dict(collections.Counter(len(s[0]) for s in allsig)))
pickle.dump(dict(allsig),open("audit2_sigs_%d.pkl"%RE,"wb"))
