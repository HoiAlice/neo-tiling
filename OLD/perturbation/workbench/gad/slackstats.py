import sys; sys.path.insert(0,'.')
import numpy as np, scheme, qstar
from schemerun import GRAPHS
for name,vb in (("K4",[0,0,1,1]),("K33",[0,0,0,1,1,1])):
    n,edges=GRAPHS[name]; L=scheme.build(n,edges); lib=qstar.library(); A,dsz=qstar.point_arrays(L); yt,yb,k=scheme.levels(L)
    Y=np.zeros(len(A)); Y[0::2]=yt; Y[1::2]=yb
    sig,act=scheme.intended_bits(L,vb); D=qstar.assemble(L,sig,act,lib,A,dsz); Q=A+D
    T=len(Y); sw_of=np.arange(T)//2; tight=0; same=0; mn=1e9; tot=0
    for a0 in range(0,T,400):
        a1=min(T,a0+400)
        sl=np.maximum(Q[None,:,0]-Q[a0:a1,None,0],Q[None,:,1]-Q[a0:a1,None,1]); mask=Y[a0:a1,None]>Y[None,:]
        for r in range(a1-a0): mask[r,a0+r]=False
        samem=(sw_of[a0:a1,None]==sw_of[None,:])
        tot+=int(mask.sum()); same+=int((mask&samem).sum())
        diff=mask&~samem; v=sl[diff]
        tight+=int((v<1e-6).sum()); pos=v[v>=1e-6]
        if len(pos): mn=min(mn,float(pos.min()))
    print(name,"conflicts",tot,"own-pair",same,"tight different-switch pairs (slack<1e-6):",tight,"min positive slack %.4f (= %.3f grid steps)"%(mn,mn/qstar.H),flush=True)
