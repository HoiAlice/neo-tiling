import sys,os; sys.path.insert(0,".")
import numpy as np
from multiprocessing import Pool
import ws_two as W
from core import weakly_solvable
eps=float(os.environ.get("WS_EPS","0.3")); NS=int(os.environ.get("WS_N","256"))
y=W.y_multi(W.K,W.SL,eps)
def job(ij): return ij,bool(weakly_solvable(W.Qcat(*ij),y))
if __name__=="__main__":
    allp=[(i,j) for i in range(16) for j in range(16)]
    rng=np.random.default_rng(0); sel=allp if NS>=256 else [allp[k] for k in rng.choice(256,NS,replace=False)]
    with Pool(9) as p: res=p.map(job,sel,chunksize=2)
    bad=[ij for ij,ok in res if not ok]
    print("D",W.D,"eps",eps,"K",W.K,"ratio %.3f"%(y.max()/y.min()),"tested",len(sel),"fail",len(bad),flush=True)
