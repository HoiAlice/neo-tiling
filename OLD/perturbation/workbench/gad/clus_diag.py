import sys, numpy as np, time
import scheme, qstar, gluelib
from clusters import *
from ysolve import find_y
if __name__=="__main__":
    L=cluster_edge(); lib=qstar.library(); A2,dsz=qstar.point_arrays(L)
    yt,yb,k=scheme.levels(L); Y=np.zeros(len(A2)); Y[0::2]=yt; Y[1::2]=yb
    res={}
    Qs={}
    for vb in [(0,1),(1,0),(0,0),(1,1)]:
        sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A2,dsz); Qs[vb]=np.exp(gluelib.snap(A2+D,1e-5))
    for vb in [(1,0),(0,0)]:
        t0=time.time(); y=find_y([Qs[vb]],Y,1e-6,100); print(vb,"free-y LP feasible:",y is not None,"max/min",None if y is None else y.max()/y.min(),"(%ds)"%(time.time()-t0),flush=True)
        if y is None:
            keep=list(range(len(L.sw)))
            for i in range(len(L.sw)):
                tr=[j for j in keep if j!=i]; ii=[2*j+c for j in tr for c in (0,1)]
                if find_y([Qs[vb][ii]],Y[ii],1e-6,100) is None: keep=tr
            print(vb,"minimal infeasible switches",keep,[ (L.meta[j]['kind'],tuple(float(z) for z in L.sw[j])) for j in keep],flush=True)
