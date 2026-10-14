import sys, pickle, time, itertools, collections
from fractions import Fraction as Fr
import numpy as np
from multiprocessing import Pool
import scheme, scheme2, qstar, gluelib
from schemerun2 import surrogate_Y
import enum2
from enum2 import GR, window
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import ws_exact2
RHO=Fr(11); GFAC=Fr(1,10); EPS=Fr(3,10)
def y_exact(sc_list,kinks,rho=RHO,gfac=GFAC,eps=EPS):
    smax=max(sc_list)
    def slope_interval(a):      # slope on (a,a+1)
        return rho**sum(1 for k in kinks if k<=a)
    def F(s):
        return sum((slope_interval(a) for a in range(int(s),int(smax)+1)),Fr(0))
    tops=[];bots=[]
    for s in sc_list:
        b=F(s); g=gfac*slope_interval(int(s)-1); bots.append(b); tops.append(b+g)
    mx=max(tops)
    return tops,bots,eps,mx
def job(args):
    kind,g,p,a,RE,G,R,rho=args
    n,edges=GR[g]; L=scheme2.build(n,edges,RE,G); lib=qstar.library(); A,dsz=qstar.point_arrays(L)
    sig,act=scheme.intended_bits(L,list(p)); D=qstar.assemble(L,sig,act,lib,A,dsz)
    ids=window(L,a,R)
    rows=[]
    for i in ids: rows+=[2*i,2*i+1]
    Q=np.exp(gluelib.snap((A+D)[rows],1e-5))
    sc=[int(L.sw[i][0]+L.sw[i][1]+L.sw[i][2]) for i in ids]
    kinks=sorted({int(L.sw[ar['idx'][0]][0]+L.sw[ar['idx'][0]][1]+4) for ar in L.arm.values()})
    lo,hi=min(sc),max(sc); kin=[k for k in kinks if lo-1<=k<=hi+1]
    tops,bots,eps,mx=y_exact(sc,kin,Fr(rho))
    y=[]
    for t,b in zip(tops,bots): y+=[1+eps*t/mx,1+eps*b/mx]
    t0=time.time()
    okf=gluelib.weak(Q,np.array([float(v) for v in y]))
    if not okf: return (kind,g,p,a,len(ids),"FLOAT-FAIL",0)
    ok,msg=ws_exact2.exact_ok(Q,y)
    return (kind,g,p,a,len(ids),"EXACT" if ok else "exact-fail:"+msg,round(time.time()-t0,1))
if __name__=="__main__":
    which=sys.argv[3] if len(sys.argv)>3 else "13"
    RE,G,R=((6,16,13.0) if which=="13" else (10,26,24.0)); rho=int(sys.argv[1]) if len(sys.argv)>1 else 11
    lim=int(sys.argv[2]) if len(sys.argv)>2 else 10**9
    types=pickle.load(open("enum2_types.pkl" if which=="13" else "enum24_types.pkl","rb"))
    jobs=[]
    for (kind,sg),d in types.items():
        for bk,(g,p,a) in d.items(): jobs.append((kind,g,p,a,RE,G,R,rho))
    print("jobs",len(jobs),flush=True)
    jobs=jobs[:lim]
    with Pool(8) as pool: out=pool.map(job,jobs,chunksize=1)
    c=collections.Counter(o[5].split(':')[0] for o in out)
    print("results",dict(c),"max window",max(o[4] for o in out),"max time",max(o[6] for o in out))
    for o in out:
        if o[5]!="EXACT": print(o)
    pickle.dump(out,open("exactcert2_out_%s.pkl"%which,"wb"))
