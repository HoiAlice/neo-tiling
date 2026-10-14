"""Remaining patterns at ideal cost: cprime 8, K3 2. time_limit 900, 10 jobs on 10 cores. Saves sigma and polished (margin 1e-8) log-coordinates."""
import sys; sys.path.insert(0,".")
import numpy as np, cx2, cprime, k3
from multiprocessing import Pool
from core import solve_dom, polish_margin
have_cp={(0,1,0,1),(0,1,1,0),(1,0,0,1),(1,0,1,0),(1,0,1,1),(0,0,1,1),(0,1,0,0),(1,0,0,0)}
import itertools
jobs=[("cp",p) for p in itertools.product((0,1),repeat=4) if p not in have_cp]+[("k3",(0,0,0)),("k3",(1,1,1))]
def job(a):
    kind,fx=a
    sw,idx=(cprime.build_c() if kind=="cp" else k3.build())
    A,Y,conf,ks=cx2.setup(sw)
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=900)
    cm,u=polish_margin(A,conf,r[1],1e-8)
    return kind,fx,r[1],cm,u
if __name__=="__main__":
    with Pool(10) as p: res=p.map(job,jobs,chunksize=1)
    np.save("ws_ser2.npy",np.array(res,dtype=object),allow_pickle=True)
    print([(r[0],r[1],round(r[3],5)) for r in res])
