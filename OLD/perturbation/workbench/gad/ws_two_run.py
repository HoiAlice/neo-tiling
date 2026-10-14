import sys; sys.path.insert(0,".")
import numpy as np
from multiprocessing import Pool
import ws_two as W
from core import weakly_solvable
import os
eps=float(os.environ.get("WS_EPS","0.3"))
y=W.y_multi(W.K,W.SL,eps)
def job(ij): return ij,bool(weakly_solvable(W.Qcat(*ij),y))
if __name__=="__main__":
    with Pool(9) as p: res=p.map(job,[(i,j) for i in range(16) for j in range(16)],chunksize=4)
    bad=[ij for ij,ok in res if not ok]
    print("D",W.D,"eps",eps,"ratio %.3f"%(y.max()/y.min()),"fail",len(bad),"of 256",[(W.pats[i],W.pats[j]) for i,j in bad[:6]],flush=True)
