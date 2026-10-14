import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from multiprocessing import Pool
import ws_two as W
from ws_rule import setup_with
from core import weakly_solvable
VAR=os.environ.get("WS_VAR","base"); EPS=float(os.environ.get("WS_EPS","0.3")); NS=int(os.environ.get("WS_N","48"))
def make_y():
    if VAR=="base": return W.y_multi(W.K,W.SL,EPS)
    if VAR.startswith("g") and not VAR.startswith("gd"): return W.y_multi(W.K,W.SL,EPS,gap=float(VAR[1:]))      # smaller gap
    if VAR.startswith("gd"):
        _,gp,m=VAR.split(":"); m=float(m); return W.y_multi(W.K,[0.02,0.02+0.05*m,0.02+0.10*m],EPS,gap=float(gp))
    if VAR.startswith("d"):                                                         # larger slope increments
        m=float(VAR[1:]); return W.y_multi(W.K,[0.02,0.02+0.05*m,0.02+0.10*m],EPS)
    if VAR.startswith("q"):                                                         # strictly concave: slope grows linearly with s
        kap=float(VAR[1:]); s=W.s; smax=s.max()
        fb=np.array([ (0.02*(smax-v)+kap*0.5*(smax-v)**2*0)+0.0 for v in s])  # placeholder replaced below
        # F(s)=int_s^smax slope(u)du, slope(u)=0.02+kap*(u-s_min)
        smin=s.min(); fb=np.array([0.02*(smax-v)+kap*0.5*((smax-smin)**2-(v-smin)**2) for v in s])
        eta=np.concatenate([[b+W.g,b] for b in fb]); return 1+EPS*eta/eta.max()
y=make_y()
def job(ij): return ij,bool(weakly_solvable(W.Qcat(*ij),y))
if __name__=="__main__":
    allp=[(i,j) for i in range(16) for j in range(16)]
    rng=np.random.default_rng(1); sel=allp if NS>=256 else [allp[k] for k in rng.choice(256,NS,replace=False)]
    A2,conf=setup_with(W.sw,y); conf=set(conf); A0,c0=setup_with(W.sw,W.y_multi(W.K,W.SL,EPS)); 
    with Pool(9) as p: res=p.map(job,sel,chunksize=2)
    print("VAR",VAR,"D",W.D,"eps",EPS,"conflict diff vs base",len(conf^set(c0)),"tested",len(sel),"fail",sum(1 for _,ok in res if not ok),flush=True)
