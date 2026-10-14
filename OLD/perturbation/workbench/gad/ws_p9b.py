"""Search Q' near Q(sigma): dominance-feasible, cost <= cost+tol, weakly solvable at fixed y. Moves of the points of the minimal obstruction on a grid."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import itertools, numpy as np, cx2, cprime
from core import weakly_solvable
sw,idx=cprime.build_c(); A,Y,conf,ks=cx2.setup(sw)
eta=np.load("ws_eta_cprime.npz")['eta']; y=1+0.1*eta
conf=np.array(conf)
def feas(L,tol=0.0):
    t,s=conf[:,0],conf[:,1]
    return bool(np.all(np.minimum(L[t,0]-L[s,0],L[t,1]-L[s,1])<=tol))
def cost(L): return float(np.sum(np.exp(np.abs(L-A))-1))
def run(Q0,obs,deltas=(1e-4,1e-3,1e-2),costtol=1e-3):
    L0=np.log(Q0); c0=cost(L0); print("base cost",c0,"feasible",feas(L0),"weak",weakly_solvable(Q0,y),flush=True)
    found=[]
    coords=[(p,k) for p in obs for k in (0,1)]
    for dl in deltas:
        n=0
        for mv in itertools.product((-1,0,1),repeat=len(coords)):
            if not any(mv): continue
            L=L0.copy()
            for (p,k),m in zip(coords,mv): L[p,k]+=m*dl
            if not feas(L): continue
            if cost(L)-c0>costtol: continue
            n+=1
            if weakly_solvable(np.exp(L)[obs],y[obs]) and weakly_solvable(np.exp(L),y): found.append((dl,mv,cost(L)-c0)); 
        print("delta",dl,"feasible moves",n,"weakly solvable ones",len(found),flush=True)
        if found: break
    return found
if __name__=="__main__":
    d=np.load("ws_all_cp.npz"); pats=[tuple(p) for p in d['pats'].tolist()]
    pat=tuple(int(c) for c in sys.argv[1]); obs=[int(v) for v in sys.argv[2].split(",")]
    f=run(d['Qs'][pats.index(pat)],obs)
    print("RESULT",pat,"found",len(f),f[:3])
