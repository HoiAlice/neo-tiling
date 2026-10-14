import sys, collections, itertools, time
import numpy as np
import scheme, qstar, gluelib
from auditclus import window
from schemerun import GRAPHS
from ysolve import find_y
def diag(g,a,R,vb):
    n,edges=GRAPHS[g]; L=scheme.build(n,edges); lib=qstar.library()
    yt,yb,k=scheme.levels(L); Y=np.zeros(2*len(L.sw)); Y[0::2]=yt; Y[1::2]=yb
    A,dsz=qstar.point_arrays(L); ids=window(L,a,R)
    sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz)
    rows=[]; 
    for i in ids: rows+=[2*i,2*i+1]
    Q=np.exp(gluelib.snap((A+D)[rows],1e-5)); Yw=Y[rows]
    print(g,a,"window",len(ids),"weak:",gluelib.weak(Q,Yw),flush=True)
    yf=find_y([Q],Yw,1e-9,100); print(" free-y LP feasible:",yf is not None,flush=True)
    keep=list(range(len(ids)))
    def fails(kp):
        r=[2*j+c for j in kp for c in (0,1)]; return not gluelib.weak(Q[r],Yw[r])
    chunk=len(keep)//2
    while chunk>=1:
        i=0
        while i<len(keep):
            tr=keep[:i]+keep[i+chunk:]
            if tr and fails(tr): keep=tr
            else: i+=chunk
        if chunk==1: break
        chunk//=2
    print(" minimal failing set",[ (ids[j],L.meta[ids[j]]['kind'],tuple(float(x) for x in L.sw[ids[j]]),sig[ids[j]]) for j in keep],flush=True)
    print(" kinks in layout:",[(e,kk) for e,kk in L.kink.items() if act.get(e)])
if __name__=="__main__":
    diag("K4",122,13.0,(0,0,0,0)); diag("K33",293,13.0,(0,0,0,0,0,0)); diag("K33",293,13.0,(0,0,0,1,0,0))
