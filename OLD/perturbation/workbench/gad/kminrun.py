import sys, pickle, time, collections
from fractions import Fraction as Fr
import numpy as np
from multiprocessing import Pool
import scheme, scheme2, qstar, gluelib, descW, exactcert2, ws_exact2, kmin
from enum2 import window
CACHE={}
def getW(R,RE,G):
    k=(R,RE,G)
    if k not in CACHE:
        n,edges,order=descW.witness(); L=scheme2.build(n,edges,RE,G,RW=int(R)); CACHE[k]=(L,qstar.library(),qstar.point_arrays(L))
    return CACHE[k]
def job(args):
    vb,a,RE,G,R,rho,exact=args
    L,lib,(A,dsz)=getW(R,RE,G)
    sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz); ids=window(L,a,R)
    rows=[]
    for i in ids: rows+=[2*i,2*i+1]
    Q=np.exp(gluelib.snap((A+D)[rows],1e-5))
    sc=[int(L.sw[i][0]+L.sw[i][1]+L.sw[i][2]) for i in ids]
    kinks=sorted({int(L.sw[ar['idx'][0]][0]+L.sw[ar['idx'][0]][1]+4) for ar in L.arm.values()}); kin=[k for k in kinks if min(sc)-1<=k<=max(sc)+1]
    tops,bots,eps,mx=exactcert2.y_exact(sc,kin,Fr(rho))
    eta=[]
    for t,b in zip(tops,bots): eta+=[t/mx,b/mx]          # Fractions in (0,1]
    etaf=np.array([float(v) for v in eta]); rng=float(max(etaf)-min(etaf))
    P=[(Fr(float(a_)),Fr(float(b_))) for a_,b_ in Q]
    bstar=kmin.kmin_lp(P,etaf)
    out=dict(window=len(ids),range=rng,b=bstar,kappa=bstar/rng)
    if exact:
        # rigorous upper bound: exact certificate at b = bstar + 1e-6*range
        bup=Fr(float(bstar+1e-6*rng)).limit_denominator(10**9)
        y=[bup+e for e in eta]
        ok,msg=ws_exact2.exact_ok(Q,y); out['exact_upper']=bool(ok)
    return out
if __name__=="__main__":
    R=float(sys.argv[1]); RE=int(sys.argv[2]); G=int(sys.argv[3]); rho=int(sys.argv[4]); exact=(sys.argv[5]=="exact")
    W=pickle.load(open("descW_all_%d.pkl"%int(R),"rb")); jobs=[]; meta=[]
    for sg,d in W.items():
        for bk,(cname,vb,a) in d.items(): jobs.append((vb,a,RE,G,R,rho,exact)); meta.append(sg)
    print("jobs",len(jobs),flush=True)
    with Pool(8) as pool: out=pool.map(job,jobs,chunksize=1)
    kap=np.array([o['kappa'] for o in out])
    print("R",R,"rho",rho,"kappa_min/range over all (type,bits) pairs: min %.4f median %.4f max %.4f"%(kap.min(),np.median(kap),kap.max()))
    if exact: print("exact upper-bound certificates:",sum(1 for o in out if o.get('exact_upper')),"of",len(out))
    pickle.dump((meta,out),open("kmin_%d_%d.pkl"%(int(R),rho),"wb"))
    order=np.argsort(-kap)[:5]
    for i in order: print("  largest kappa",round(kap[i],4),"window",out[i]['window'],"range",out[i]['range'])
