import sys; sys.path.insert(0,".")
import numpy as np, cx2, cprime
from multiprocessing import Pool
from core import solve_dom, polish_margin
sw,idx=cprime.build_c()
def job(fx):
    A,Y,conf,ks=cx2.setup(sw)
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=900)
    cm,u=polish_margin(A,conf,r[1],1e-6)
    return fx,r[1],r[2],cm,u,A,Y,conf
if __name__=="__main__":
    pats=[(1,0,1,1),(0,0,1,1),(0,1,0,0),(1,0,0,0)]
    with Pool(4) as p: res=p.map(job,pats,chunksize=1)
    np.savez("ws_ser.npz",pats=np.array([r[0] for r in res]),sigma=np.array([r[1] for r in res]),cost=np.array([r[3] for r in res]),
             lb=np.array([r[2] for r in res]),Qs=np.array([np.exp(r[4]) for r in res]),A=res[0][5],Y=res[0][6],conf=np.array(res[0][7]))
    print([(r[0],round(r[3],5)) for r in res])
