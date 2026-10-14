"""Rebuild K3 optimal Qs (6 optimal patterns) in parallel and save (Qs, Y, found y). Uses k3.py, cx2, ysolve unmodified."""
import sys; sys.path.insert(0,".")
from k3 import *
from multiprocessing import Pool
FX=[(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0)]
def job(fx):
    sw,idx=build(); A,Y,conf,ks=cx2.setup(sw)
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=500)
    cm,u=polish_margin(A,conf,r[1],1e-6); return np.exp(u),cm
if __name__=="__main__":
    with Pool(6) as p: res=p.map(job,FX)
    Qs=[r[0] for r in res]; print([round(r[1],5) for r in res],flush=True)
    sw,idx=build(); A,Y,conf,ks=cx2.setup(sw)
    y=find_y(Qs,Y,1e-6,1.9)
    np.savez("ws_k3.npz",Qs=np.array(Qs),Y=Y,y=y,A=A)
    print("saved",y.max()/y.min())
