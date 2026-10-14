import sys, itertools, time, numpy as np
import scheme, qstar, gluelib
from gluelib import cx2
def cluster_edge(bus_gap=24):
    scheme.BUS_GAP=bus_gap
    L=scheme.build(2,[(0,1)])
    return L
def run_scheme_cluster(L,name,patterns):
    yt,yb,kinks=scheme.levels(L)
    swl=[(float(bx),float(by),d,float(t),float(b)) for (bx,by,d),t,b in zip(L.sw,yt,yb)]
    A,Y,conf,ks=gluelib.setup(swl); n=len(L.sw)
    print(name,"switches",n,"points",2*n,"conflicts",len(conf),"kink levels",kinks,flush=True)
    sumB=sum(gluelib.B(d) for (_,_,d) in L.sw)
    lib=qstar.library(); A2,dsz=qstar.point_arrays(L)
    for vb in patterns:
        sig,act=scheme.intended_bits(L,list(vb))
        D=qstar.assemble(L,sig,act,lib,A2,dsz); c=qstar.cost(D); nv=qstar.check(A2,D,np.concatenate([[0]*0,Y]) if False else Y)['violations']
        u=np.log(np.exp(A2+D)); Q=np.exp(gluelib.snap(A2+D,1e-5))
        unc=sum(1 for (i,j) in L.edges if vb[i]==vb[j]); nx=len(L.crossings)
        exp=sumB+nx*0.1229644+unc*0.0493902
        t0=time.time(); w=gluelib.weak(Q,Y)
        print(name,vb,"cost-closed %.2e"%(c-exp),"violations",nv,"weakly solvable:",w,"(%ds)"%(time.time()-t0),flush=True)
if __name__=="__main__":
    which=sys.argv[1]
    if which=="edge":
        L=cluster_edge(); run_scheme_cluster(L,"C2 edge (bus-arm-corner-halflink track-corner-arm-bus)",list(itertools.product((0,1),repeat=2)))
