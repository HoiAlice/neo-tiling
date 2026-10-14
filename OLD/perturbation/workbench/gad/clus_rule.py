import sys, numpy as np, time
import scheme, qstar, gluelib, planar
from fractions import Fraction
from clusters import *
def levels2(L,c1,Delta,g,kinks,eps=0.3):
    sc=np.array([float(x[0]+x[1]+x[2]) for x in L.sw]); smax=sc.max()+1
    F=1+c1*(smax-sc)
    for k in kinks: F=F+Delta*np.maximum(0.0,smax-np.maximum(sc,k))
    top=F+g; m=top.max(); return 1+eps*top/m,1+eps*F/m
if __name__=="__main__":
    L=cluster_edge(); lib=qstar.library(); A2,dsz=qstar.point_arrays(L)
    arm_k=sorted({float(L.sw[a['idx'][0]][0]+L.sw[a['idx'][0]][1]+4) for a in L.arm.values()})
    # corner levels: s_c of K (u0) for both arms
    corner_k=sorted({float(L.sw[a['idx'][-1]][0]+L.sw[a['idx'][-1]][1]+4) for a in L.arm.values()})
    print("arm levels",arm_k,"corner levels",corner_k)
    Qs={}
    for vb in [(1,0),(0,0)]:
        sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A2,dsz); Qs[vb]=np.exp(gluelib.snap(A2+D,1e-5))
    graphs={}
    for vb,Q in Qs.items():
        Pf=[tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q]
        graphs[vb]=(Pf,planar.chain_graph(Pf))
    rules=[("base c1=.02 D=.6 g=.002",0.02,0.6,0.002,arm_k),
           ("D=2",0.02,2.0,0.002,arm_k),("D=6",0.02,6.0,0.002,arm_k),
           ("g=.0002",0.02,0.6,0.0002,arm_k),("D=6,g=.0002",0.02,6.0,0.0002,arm_k),
           ("kinks arm+corner",0.02,0.6,0.002,sorted(set(arm_k+corner_k))),
           ("c1=.2",0.2,0.6,0.002,arm_k)]
    for name,c1,Dl,g,ks_ in rules:
        yt,yb=levels2(L,c1,Dl,g,ks_); Y=np.zeros(len(A2)); Y[0::2]=yt; Y[1::2]=yb
        out=[]
        for vb in graphs:
            Pf,gr=graphs[vb]; yf=[Fraction(float(v)).limit_denominator(10**12) for v in Y]
            out.append((vb,planar.flow_lp(Pf,yf,graph=gr).feasible))
        print(name,out,flush=True)
