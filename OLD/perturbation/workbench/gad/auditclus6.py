import sys, itertools, numpy as np
import scheme, qstar, gluelib
from auditclus import window
from schemerun import GRAPHS
def localy(L,ids,kinks_all,slope0,delta,g=0.002,eps=0.3):
    sc=np.array([float(L.sw[i][0]+L.sw[i][1]+L.sw[i][2]) for i in ids]); lo,hi=sc.min()-1,sc.max()+1
    ks=[k for k in kinks_all if lo<=k<=hi]
    # F decreasing in s: F(s)=Fc + slope0*(hi-s) + sum_k delta_k*max(0,hi-max(s,k)) ; delta may be list
    F=slope0*(hi-sc)
    for q,k in enumerate(ks):
        d=delta[q] if isinstance(delta,(list,tuple)) else delta
        F=F+d*np.maximum(0.0,hi-np.maximum(sc,k))
    tops=F+g; m=tops.max()
    return 1+eps*tops/m,1+eps*F/m,ks
if __name__=="__main__":
    g_,a,vb=("K33",293,(0,0,0,0,0,0))
    n,edges=GRAPHS[g_]; L=scheme.build(n,edges); lib=qstar.library(); A,dsz=qstar.point_arrays(L)
    yt0,yb0,kinks=scheme.levels(L)
    ids=window(L,a,13.0); sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz)
    rows=[]
    for i in ids: rows+=[2*i,2*i+1]
    Q=np.exp(gluelib.snap((A+D)[rows],1e-5))
    sc=[float(L.sw[i][0]+L.sw[i][1]+L.sw[i][2]) for i in ids]; print("window s_c range",min(sc),max(sc),"kinks inside",[k for k in kinks if min(sc)-1<=k<=max(sc)+1],"kinks below window",sum(1 for k in kinks if k<min(sc)-1),flush=True)
    k0=sum(1 for k in kinks if k<min(sc)-1)
    cases=[("global rule slope c1+k0*0.6, delta .6",0.02+k0*0.6,0.6),("slope .02, delta .6",0.02,0.6),("slope .02, delta 6",0.02,6.0),
           ("global slope, delta = 30*slope",0.02+k0*0.6,30*(0.02+k0*0.6)),("slope .02, delta .6, g=.0002",0.02,0.6)]
    for name,s0,dl in cases:
        for gg in (0.002,0.0002):
            for eps in (0.3,0.02):
                yt,yb,ks=localy(L,ids,kinks,s0,dl,gg,eps); Y=np.zeros(len(rows)); Y[0::2]=yt; Y[1::2]=yb
                print(name,"g",gg,"eps",eps,"->",gluelib.weak(Q,Y),flush=True)
