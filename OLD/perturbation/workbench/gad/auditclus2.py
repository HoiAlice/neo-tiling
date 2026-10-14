import sys, collections
import numpy as np
import scheme
from auditclus import *
import schemerun
GR=dict(schemerun.GRAPHS)
GR["Q3"]=(8,[(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)])
GR["Petersen"]=(10,[(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)])
GR["Prism"]=(6,[(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)])
for k in list(GR): GR[k]=(GR[k][0],[tuple(sorted(e)) for e in GR[k][1]])
schemerun.GRAPHS=GR
import auditclus; auditclus.GRAPHS=GR
if __name__=="__main__":
    R=float(sys.argv[1]); seen=collections.defaultdict(set); growth=[]
    for gs in (("K3",),("K4",),("K33",),("Q3",),("Petersen",),("Prism",)):
        t=auditclus.enum(R,graphs=gs)
        for (kind,sig) in t: seen[kind].add(sig)
        growth.append((gs[0],{k:len(v) for k,v in seen.items()}))
    for g in growth: print(g)
