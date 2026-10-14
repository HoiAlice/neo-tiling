import sys, pickle, time, collections
from fractions import Fraction as Fr
import numpy as np
from multiprocessing import Pool
import scheme, scheme2, qstar, gluelib
import descW, exactcert2, ws_exact2
from enum2 import window
CACHE={}
def getW(R,RE,G):
    k=(R,RE,G)
    if k not in CACHE:
        n,edges,order=descW.witness(); L=scheme2.build(n,edges,RE,G,RW=int(R)); CACHE[k]=(L,qstar.library(),qstar.point_arrays(L))
    return CACHE[k]
def job(args):
    kind,vb,a,RE,G,R,rho=args
    L,lib,(A,dsz)=getW(R,RE,G)
    sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz); ids=window(L,a,R)
    rows=[]
    for i in ids: rows+=[2*i,2*i+1]
    Q=np.exp(gluelib.snap((A+D)[rows],1e-5))
    sc=[int(L.sw[i][0]+L.sw[i][1]+L.sw[i][2]) for i in ids]
    kinks=sorted({int(L.sw[ar['idx'][0]][0]+L.sw[ar['idx'][0]][1]+4) for ar in L.arm.values()}); kin=[k for k in kinks if min(sc)-1<=k<=max(sc)+1]
    tops,bots,eps,mx=exactcert2.y_exact(sc,kin,Fr(rho))
    y=[]
    for t,b in zip(tops,bots): y+=[1+eps*t/mx,1+eps*b/mx]
    t0=time.time()
    if not gluelib.weak(Q,np.array([float(v) for v in y])): return (kind,a,len(ids),"FLOAT-FAIL",0)
    ok,msg=ws_exact2.exact_ok(Q,y)
    return (kind,a,len(ids),"EXACT" if ok else "exact-fail:"+msg,round(time.time()-t0,1))
if __name__=="__main__":
    R=float(sys.argv[1]); RE=int(sys.argv[2]); G=int(sys.argv[3]); rho=int(sys.argv[4])
    W=pickle.load(open("descW_all_%d.pkl"%int(R),"rb")); jobs=[]
    for sg,d in W.items():
        kind="any"
        for bk,(cname,vb,a) in d.items(): jobs.append((kind,vb,a,RE,G,R,rho))
    print("jobs",len(jobs),flush=True)
    with Pool(8) as pool: out=pool.map(job,jobs,chunksize=1)
    c=collections.Counter(o[3].split(':')[0] for o in out)
    print("R",R,"rho",rho,"results",dict(c),"max window",max(o[2] for o in out),"max time",max(o[4] for o in out))
    for o in out:
        if o[3]!="EXACT": print(o)
