import sys, numpy as np
import scheme, qstar, gluelib
from clusters import *
from ysolve import find_y
if __name__=="__main__":
    L=cluster_edge(); lib=qstar.library(); A2,dsz=qstar.point_arrays(L)
    yt,yb,k=scheme.levels(L); Y=np.zeros(len(A2)); Y[0::2]=yt; Y[1::2]=yb
    sig,act=scheme.intended_bits(L,[1,0]); D=qstar.assemble(L,sig,act,lib,A2,dsz); Q=np.exp(gluelib.snap(A2+D,1e-5))
    y=find_y([Q],Y,1e-6,1.2)
    sc=np.array([float(x[0]+x[1]+x[2]) for x in L.sw])
    g=np.median(y[0::2]-y[1::2]); print("gap",g)
    u=sorted(set(sc)); 
    bot={}
    for i in range(len(sc)): bot.setdefault(sc[i],set()).add(round(y[2*i+1],12))
    prev=None
    for s in u:
        v=sorted(bot[s],reverse=True)[0]
        if prev is not None: print("s_c %5.1f  drop to next level (in gaps): %.2f   kinds %s"%(s,(prev-v)/g/(s-ps),sorted({L.meta[i]['kind'] for i in range(len(sc)) if sc[i]==s})))
        prev=v; ps=s
