"""Q(sigma) for every vertex-bit pattern (MILP vertex bits fixed, rest free, then polish_margin). Saves ws_all_k3.npz / ws_all_cp.npz"""
import sys; sys.path.insert(0,".")
import itertools, numpy as np
from multiprocessing import Pool
import cx2
from core import solve_dom, polish_margin
which=sys.argv[1]
if which=="k3":
    import k3; sw,idx=k3.build(); nb=3
else:
    import cprime; sw,idx=cprime.build_c(); nb=4
def job(fx):
    A,Y,conf,ks=cx2.setup(sw)
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=500)
    cm,u=polish_margin(A,conf,r[1],1e-6); return fx,np.exp(u),cm
if __name__=="__main__":
    pats=list(itertools.product((0,1),repeat=nb))
    with Pool(8) as p: res=p.map(job,pats,chunksize=1)
    A,Y,conf,ks=cx2.setup(sw)
    np.savez("ws_all_%s.npz"%which,Qs=np.array([r[1] for r in res]),pats=np.array([r[0] for r in res]),cost=np.array([r[2] for r in res]),Y=Y,A=A)
    print([(r[0],round(r[2],5)) for r in res])
