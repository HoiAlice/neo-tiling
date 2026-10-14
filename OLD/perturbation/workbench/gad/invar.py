import sys, pickle, collections
from fractions import Fraction as Fr
import numpy as np
from multiprocessing import Pool
import scheme, scheme2, qstar, gluelib
import exactcert2
from enum2 import GR, window
def job(args):
    kind,g,p,a,RE,G,R=args
    n,edges=GR[g]; L=scheme2.build(n,edges,RE,G); lib=qstar.library(); A,dsz=qstar.point_arrays(L)
    sig,act=scheme.intended_bits(L,list(p)); D=qstar.assemble(L,sig,act,lib,A,dsz); ids=window(L,a,R)
    rows=[]
    for i in ids: rows+=[2*i,2*i+1]
    Q=np.exp(gluelib.snap((A+D)[rows],1e-5))
    sc=[int(L.sw[i][0]+L.sw[i][1]+L.sw[i][2]) for i in ids]
    kinks=sorted({int(L.sw[ar['idx'][0]][0]+L.sw[ar['idx'][0]][1]+4) for ar in L.arm.values()}); kin=[k for k in kinks if min(sc)-1<=k<=max(sc)+1]
    tops,bots,eps,mx=exactcert2.y_exact(sc,kin)
    yb=[]
    for t,b in zip(tops,bots): yb+=[t/mx,b/mx]          # eta in [0,1]
    eta=np.array([float(v) for v in yb]); res={}
    for e in (0.3,0.03,0.003,1e-4): res["eps=%g"%e]=gluelib.weak(Q,1+e*eta)
    y0=1+0.3*eta
    for a_ in (1e-3,1e3): res["scale %g"%a_]=gluelib.weak(Q,a_*y0)
    for b_ in (0.5,5.0): res["+%g*1"%b_]=gluelib.weak(Q,y0+b_)
    res["-0.99*min y (shift down)"]=gluelib.weak(Q,y0-0.99*y0.min())
    return res
if __name__=="__main__":
    types=pickle.load(open("enum2_types.pkl","rb")); jobs=[]
    for (kind,sg),d in types.items():
        bk,(g,p,a)=next(iter(d.items())); jobs.append((kind,g,p,a,6,16,13.0))
    with Pool(8) as pool: out=pool.map(job,jobs,chunksize=1)
    keys=out[0].keys()
    for k in keys: print(k,"True for",sum(1 for o in out if o[k]),"of",len(out),"type representatives")
