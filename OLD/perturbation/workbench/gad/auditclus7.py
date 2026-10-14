import sys, collections, itertools, time
import numpy as np
from multiprocessing import Pool
import scheme, qstar, gluelib
from auditclus import anchors, window, enum
from schemerun import GRAPHS
RULE={}
def ylevels(L,rule):
    sc=np.array([float(x[0]+x[1]+x[2]) for x in L.sw]); kinks=sorted({float(L.sw[a['idx'][0]][0]+L.sw[a['idx'][0]][1]+4) for a in L.arm.values()})
    smax=sc.max()+1; c1,Delta,g,w=rule
    F=1+c1*(smax-sc)
    for k in kinks:
        if w is None: F=F+Delta*np.maximum(0.0,smax-np.maximum(sc,k))
        else: F=F+Delta*np.maximum(0.0,np.minimum(smax,k+w)-np.maximum(sc,k))
    top=F+g; m=top.max(); return 1+0.3*top/m,1+0.3*F/m
def job(args):
    g,aidx,ids,vb,kind,rule=args
    n,edges=GRAPHS[g]; L=scheme.build(n,edges); lib=qstar.library()
    yt,yb=ylevels(L,rule); Y=np.zeros(2*len(L.sw)); Y[0::2]=yt; Y[1::2]=yb
    A,dsz=qstar.point_arrays(L); sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz)
    rows=[]
    for i in ids: rows+=[2*i,2*i+1]
    Q=np.exp(gluelib.snap((A+D)[rows],1e-5)); return (kind,g,aidx,vb,gluelib.weak(Q,Y[rows]))
if __name__=="__main__":
    R=float(sys.argv[1]); rule=(float(sys.argv[2]),float(sys.argv[3]),float(sys.argv[4]),None if sys.argv[5]=='None' else float(sys.argv[5]))
    t=enum(R); jobs=[]
    for (kind,sig),occ in t.items():
        g,a,nn=occ[0]; n,edges=GRAPHS[g]; L=scheme.build(n,edges); ids=window(L,a,R); seen={}
        for vb in itertools.product((0,1),repeat=n):
            s_,act=scheme.intended_bits(L,list(vb)); key=tuple(s_[i] for i in ids)
            if key not in seen: seen[key]=vb
        for key,vb in seen.items(): jobs.append((g,a,ids,vb,kind,rule))
    with Pool(6) as p: out=p.map(job,jobs,chunksize=1)
    bad=[o for o in out if not o[4]]
    print("rule (c1,Delta,g,bump width)",rule,"R",R,"windows tested",len(out),"failures",len(bad),[ (o[0],o[1],o[2]) for o in bad[:6]],flush=True)
