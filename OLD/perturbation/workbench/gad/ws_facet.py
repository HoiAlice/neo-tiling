"""Binding facet (dual lambda of the gmax LP) for the final rule: support, F-part, ballast count."""
import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
import ws_two as W
from ws_gmax import gmax
mult=float(os.environ.get("WS_M","12")); slopes=[0.02,0.02+0.05*mult,0.02+0.10*mult]
fb=np.array([W.F_pw(v,W.K,slopes) for v in W.s]); scale=fb.max()+0.01; F=1+0.3*np.repeat(fb,2)/scale; tau=np.tile([1.0,0.0],len(fb))
Ab=np.vstack([np.load("ws_snap_cp.npz")['A']]*2)/0.2; Ab[2*W.n1:]+=W.D
rng=np.random.default_rng(int(os.environ.get("WS_SEED","7"))); allp=[(i,j) for i in range(16) for j in range(16)]
sel=[allp[k] for k in rng.choice(256,int(os.environ.get("WS_N","4")),replace=False)]
res=[]
for ij in sel:
    r=gmax(W.Qcat(*ij),F,tau,return_dual=True)
    if r is None: print(ij,"F not weakly solvable"); continue
    res.append((r[0],ij,r[1]))
res.sort(key=lambda x:x[0]); print("gmax over",len(res),"patterns: min %.2e median %.2e"%(res[0][0],np.median([x[0] for x in res])),flush=True)
for t,ij,lam in res[:int(os.environ.get("WS_SHOW","2"))]:
    if lam@(F-1)<0: lam=-lam
    lam=lam/np.abs(lam).max(); supp=[q for q in range(len(F)) if abs(lam[q])>1e-7]
    sw_sup=sorted(set(q//2 for q in supp)); pairs=[i for i in sw_sup if lam[2*i]<-1e-7 and lam[2*i+1]>1e-7]
    print("pattern",W.pats[ij[0]],W.pats[ij[1]],"gmax %.2e"%t,"support",len(supp),"points /",len(sw_sup),"switches; lam(tau)=%.3f"%(lam@tau),"tight pairs:",len(pairs),flush=True)
    for q in supp[:40]:
        i=q//2; print("   %+.3f c%d s%d%s s_c=%d (x,y)=(%.1f,%.1f) t=%.1f"%(lam[q],i//W.n1,i%W.n1,"t" if q%2==0 else "b",W.s[i],Ab[q,0],Ab[q,1],Ab[q,1]-Ab[q,0]))
