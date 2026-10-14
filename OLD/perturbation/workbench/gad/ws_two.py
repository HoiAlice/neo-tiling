"""Two disjoint cprime copies at s offset 2*D; multi-kink concave F; rho_dom by concatenation (feasibility of cross conflicts) and snapped weak solvability at all 256 patterns."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, itertools, cx2
from multiprocessing import Pool
from ws_rule import build, sc, setup_with, g
from core import weakly_solvable
import os
D=float(os.environ.get("WS_D","12")); DX=float(os.environ.get("WS_DX",D)); DY=float(os.environ.get("WS_DY",D))
sw1=build("cp"); sw2=[(bx+DX,by+DY,d,yt,yb) for bx,by,d,yt,yb in sw1]; sw=sw1+sw2; n1=len(sw1)
s=sc(sw)
def F_pw(v,kinks,slopes):   # decreasing, concave: slope slopes[0] left of kinks[0], slopes[i] between kink i-1 and i ...
    smax=s.max(); val=0.0; cuts=[-1e9]+list(kinks)+[1e9]
    for i,sl in enumerate(slopes):
        a,b=cuts[i],cuts[i+1]; lo=max(a,v); hi=min(b,smax)
        if hi>lo: val+=sl*(hi-lo)
    return val
def y_multi(kinks,slopes,eps,gap=g):
    fb=np.array([F_pw(v,kinks,slopes) for v in s]); top=fb+gap
    eta=np.concatenate([[t,b] for t,b in zip(top,fb)]); eta=eta/eta.max()
    return 1+eps*eta
K=[4,4+DX+DY]; SL=[0.02,0.07,0.12]
Q1=np.load("ws_snap_cp.npz"); pats=Q1['pats'].tolist(); Qs=Q1['Qs']
sh=np.exp(cx2.EPS*np.array([DX,DY]))
def Qcat(i,j): return np.vstack([Qs[i],Qs[j]*sh])
if __name__=="__main__":
    y=y_multi(K,SL,0.3)
    A2,conf=setup_with(sw,y); conf=np.array(conf)
    # conflict-set check: within copy1 and within copy2 vs single-copy rule
    from ws_rule4 import y_pw
    A1,c1=setup_with(sw1,y_pw(sw1,0.02,0.07,4)); S1=set(c1)
    inc1={(a,b) for a,b in conf if a<2*n1 and b<2*n1}; inc2={(a-2*n1,b-2*n1) for a,b in conf if a>=2*n1 and b>=2*n1}
    cross=[(a,b) for a,b in conf if (a<2*n1)!=(b<2*n1)]
    print("D",D,"s ranges",s[:n1].min(),s[:n1].max(),s[n1:].min(),s[n1:].max())
    print("copy1 conflicts",len(inc1),"vs single",len(S1),"diff",len(inc1^S1),"| copy2 vs single diff",len(inc2^S1),"| cross",len(cross),"directions: copy1 higher:",sum(1 for a,b in cross if a<2*n1))
    bad=0; tot=0
    for i in range(16):
        for j in range(16):
            Q=Qcat(i,j); tot+=1
            if np.any(np.minimum(Q[conf[:,0],0]-Q[conf[:,1],0],Q[conf[:,0],1]-Q[conf[:,1],1])>1e-9): bad+=1
    print("cross/all conflicts violated by concatenation: patterns",bad,"of",tot,flush=True)
    np.savez("ws_two_y.npz",y=y)
    print("copy2 extra (not in single):",sorted(inc2-S1)[:10],"missing:",sorted(S1-inc2)[:10])
