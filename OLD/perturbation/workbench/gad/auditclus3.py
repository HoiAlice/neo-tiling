import sys, collections, itertools, time
import numpy as np
from multiprocessing import Pool
import scheme, qstar, gluelib
import auditclus
from auditclus import anchors, window, enum
from schemerun import GRAPHS
def job(args):
    g,aidx,ids,bits,kind=args
    n,edges=GRAPHS[g]; L=scheme.build(n,edges); lib=qstar.library()
    yt,yb,k=scheme.levels(L); Y=np.zeros(2*len(L.sw)); Y[0::2]=yt; Y[1::2]=yb
    A,dsz=qstar.point_arrays(L)
    vb=bits[0]; sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz)
    rows=[]; 
    for i in ids: rows+=[2*i,2*i+1]
    Q=np.exp(gluelib.snap((A+D)[rows],1e-5)); Yw=Y[rows]
    t0=time.time(); ok=gluelib.weak(Q,Yw)
    return (kind,g,aidx,len(ids),tuple(sig[i] for i in ids),vb,ok,round(time.time()-t0,1))
if __name__=="__main__":
    R=float(sys.argv[1]); t=enum(R)
    jobs=[]; counts=collections.Counter()
    for (kind,sig),occ in t.items():
        g,a,nn=occ[0]
        n,edges=GRAPHS[g]; L=scheme.build(n,edges); ids=window(L,a,R)
        # local bit patterns over all global patterns of that graph
        seen={}
        for vb in itertools.product((0,1),repeat=n):
            s_,act=scheme.intended_bits(L,list(vb)); key=tuple(s_[i] for i in ids)
            if key not in seen: seen[key]=(vb,)
        for key,bits in seen.items(): jobs.append((g,a,ids,bits,kind))
        counts[kind]+=len(seen)
    print("R",R,"window types",len(t),"local patterns per kind",dict(counts),"total LPs",len(jobs),flush=True)
    with Pool(6) as p: out=p.map(job,jobs,chunksize=1)
    bad=[o for o in out if not o[6]]
    print("weakly solvable:",len(out)-len(bad),"of",len(out),"failures",len(bad))
    for o in bad[:10]: print("FAIL",o)
    print("max LP time",max(o[7] for o in out))
