import sys, numpy as np
import scheme, qstar, gluelib
from clusters import *
from ysolve import find_y
if __name__=="__main__":
    L=cluster_edge(); lib=qstar.library(); A2,dsz=qstar.point_arrays(L)
    yt,yb,k=scheme.levels(L); Y=np.zeros(len(A2)); Y[0::2]=yt; Y[1::2]=yb
    sig,act=scheme.intended_bits(L,[1,0]); D=qstar.assemble(L,sig,act,lib,A2,dsz); Q=np.exp(gluelib.snap(A2+D,1e-5))
    for cap in (1.9,1.5,1.2):
        y=find_y([Q],Y,1e-6,cap); print("cap",cap,"feasible",y is not None,flush=True)
        if y is not None and cap==1.2:
            sc=np.array([float(x[0]+x[1]+x[2]) for x in L.sw]); o=np.argsort(sc)
            last=None
            for i in o:
                row=(sc[i],L.meta[i]['kind'],round(y[2*i+1],5),round(y[2*i]-y[2*i+1],6))
                if (row[0],row[2])!=last: print(row)
                last=(row[0],row[2])
