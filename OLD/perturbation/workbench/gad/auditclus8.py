import sys, collections, itertools
import numpy as np
from multiprocessing import Pool
import scheme, qstar, gluelib
from auditclus import window, enum
from schemerun import GRAPHS
def ygeo(L,ids,kinks,rho,c1=0.02,g=0.002,eps=0.3):
    sc=np.array([float(L.sw[i][0]+L.sw[i][1]+L.sw[i][2]) for i in ids]); lo,hi=sc.min()-1,sc.max()+1
    k0=sum(1 for k in kinks if k<lo); ks=[k for k in kinks if lo<=k<=hi]
    slope=c1*rho**k0
    # build F by integrating slope(u): slope = slope0 on (lo, first kink), multiplied by rho after each kink (increasing toward NE)
    pts=[lo]+ks+[hi]; slopes=[slope*rho**q for q in range(len(ks)+1)]
    F=np.zeros(len(sc))
    for q in range(len(pts)-1):
        a,b=pts[q],pts[q+1]; seg=np.clip(np.minimum(hi,b)-np.maximum(sc,a),0,None)   # integral from s to hi of slope(u) du restricted to [a,b]
        F=F+slopes[q]*seg
    F=F+1e-9
    tops=F+g*slopes[0]*0+ g*0   # gap g absolute scaled below
    # gap must stay below curvature: use g relative to local base slope (g/c1 = 0.1)
    gl=0.1*slope; tops=F+gl; m=tops.max()
    return 1+eps*tops/m,1+eps*F/m
def job(args):
    g,aidx,ids,vb,kind,rho=args
    n,edges=GRAPHS[g]; L=scheme.build(n,edges); lib=qstar.library(); A,dsz=qstar.point_arrays(L)
    kinks=sorted({float(L.sw[a['idx'][0]][0]+L.sw[a['idx'][0]][1]+4) for a in L.arm.values()})
    sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz)
    rows=[]
    for i in ids: rows+=[2*i,2*i+1]
    Q=np.exp(gluelib.snap((A+D)[rows],1e-5)); yt,yb=ygeo(L,ids,kinks,rho)
    Y=np.zeros(len(rows)); Y[0::2]=yt; Y[1::2]=yb
    return (kind,g,aidx,vb,gluelib.weak(Q,Y))
if __name__=="__main__":
    R=float(sys.argv[1]); rho=float(sys.argv[2]); t=enum(R); jobs=[]
    for (kind,sig),occ in t.items():
        g,a,nn=occ[0]; n,edges=GRAPHS[g]; L=scheme.build(n,edges); ids=window(L,a,R); seen={}
        for vb in itertools.product((0,1),repeat=n):
            s_,act=scheme.intended_bits(L,list(vb)); key=tuple(s_[i] for i in ids)
            if key not in seen: seen[key]=vb
        for key,vb in seen.items(): jobs.append((g,a,ids,vb,kind,rho))
    with Pool(6) as p: out=p.map(job,jobs,chunksize=1)
    bad=[o for o in out if not o[4]]
    print("geometric-slope rule rho",rho,"R",R,"windows tested",len(out),"failures",len(bad),[(o[0],o[1],o[2]) for o in bad[:6]],flush=True)
