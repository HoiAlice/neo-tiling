import sys, numpy as np, time
import scheme, qstar, gluelib
from clusters import *
def fails(L,Q,Y,keep):
    ii=[2*j+c for j in keep for c in (0,1)]
    return not gluelib.weak(Q[ii],Y[ii])
if __name__=="__main__":
    vb=tuple(int(c) for c in sys.argv[1])
    L=cluster_edge(); lib=qstar.library(); A2,dsz=qstar.point_arrays(L)
    yt,yb,k=scheme.levels(L); Y=np.zeros(len(A2)); Y[0::2]=yt; Y[1::2]=yb
    sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A2,dsz); Q=np.exp(gluelib.snap(A2+D,1e-5))
    keep=list(range(len(L.sw)))
    assert fails(L,Q,Y,keep)
    chunk=len(keep)//2
    t0=time.time()
    while chunk>=1:
        i=0; changed=False
        while i<len(keep):
            trial=keep[:i]+keep[i+chunk:]
            if trial and fails(L,Q,Y,trial): keep=trial; changed=True
            else: i+=chunk
        print("chunk",chunk,"keep",len(keep),"t",round(time.time()-t0),flush=True)
        if chunk==1 and not changed: break
        chunk=max(1,chunk//2) if chunk>1 else (1 if changed else 0)
        if chunk==0: break
    print("MINIMAL failing switch set",keep)
    for j in keep: print(j,L.meta[j],tuple(float(x) for x in L.sw[j]),"bit",sig[j],"level yb %.6f"%Y[2*j+1])
