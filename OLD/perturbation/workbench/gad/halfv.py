import numpy as np
from gluelib import *
from relay import build_relay_cp
def run(shift):
    sw,idx=build_relay_cp(); sw=[(a,b,c) for (a,b,c,_,_) in sw]
    if shift:
        for i in (2,3,8): sw[i]=(sw[i][0]-0.5,sw[i][1]-0.5,sw[i][2])
    out=[]
    for b in (0,1):
        sig=[None]*len(sw)
        for i in (0,1,2,3,8,4,6,9,11): sig[i]=b
        for i in (5,7,10,12): sig[i]=b^1
        swl=rule_levels(sw,[]); A,Y,conf,ks=setup(swl)
        u,c,nv=glue(A,conf,ks,sig); Q=np.exp(snap(u,1e-5))
        out.append((b,round(c-sum(B(d) for (_,_,d) in sw),8),nv,weak(Q,Y)))
    return out
if __name__=="__main__":
    print("unshifted V chain:",run(False),flush=True)
    print("V link 3->vertex and 2->3 shifted by 0.5 (parity flip):",run(True),flush=True)
