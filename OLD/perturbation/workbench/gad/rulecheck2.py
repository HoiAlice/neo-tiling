import sys; sys.path.insert(0,'.')
import numpy as np, scheme, qstar
from schemerun import GRAPHS
D2=2*0.6272
for name in ("K3","K4","K33"):
    n,edges=GRAPHS[name]; L=scheme.build(n,edges); A,dsz=qstar.point_arrays(L); yt,yb,k=scheme.levels(L)
    Y=np.zeros(len(A)); Y[0::2]=yt; Y[1::2]=yb
    cx=np.array([float(x[0]+x[2]/2) for x in L.sw]); cy=np.array([float(x[1]+x[2]/2) for x in L.sw])
    T=len(A); worst=0.0; cnt=0; total=0; sw_of=np.arange(T)//2
    hist={}
    for a0 in range(0,T,400):
        a1=min(T,a0+400)
        m=np.maximum(A[None,:,0]-A[a0:a1,None,0],A[None,:,1]-A[a0:a1,None,1])    # original margin: max_c (P_b - P_a)
        mask=(Y[a0:a1,None]>Y[None,:])&(m<D2)
        for r in range(a1-a0): mask[r,a0+r]=False
        ii,jj=np.nonzero(mask)
        ia=(a0+ii)//2; ib=jj//2
        dist=np.maximum(np.abs(cx[ia]-cx[ib]),np.abs(cy[ia]-cy[ib]))
        if len(dist): worst=max(worst,float(dist.max())); cnt+=len(dist)
        total+=int(((Y[a0:a1,None]>Y[None,:])).sum())
    print(name,"conflicts with original margin < 2D (6.43 steps):",cnt,"of",total,"; max L-inf distance of box centres among them: %.2f grid units"%worst,flush=True)
