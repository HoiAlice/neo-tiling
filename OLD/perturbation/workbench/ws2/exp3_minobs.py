"""Minimal infeasible point subset for the ridge-family LP (deletion filter)."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"../gad"); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from axcone import cone_lp, AX
from ws_rule import build, sc
from ws_rule4 import y_pw
kind="cp"; sw=build(kind); d=np.load("../gad/ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
y=y_pw(sw,0.02,0.07,4,gap=0.01); s=sc(sw)
dirs=AX+[(1.,1.)]
def nm(q): return "s%d%s"%(q//2,"t" if q%2==0 else "b")
pi=int(sys.argv[1]) if len(sys.argv)>1 else 0
Q=Qs[pi]; L=np.log(Q); T=len(y)
keep=list(range(T))
def infeas(idx):
    ok,info=cone_lp(L[idx],y[idx],dirs,margin=True); return not ok
assert infeas(keep)
for q in list(keep):
    trial=[k for k in keep if k!=q]
    if infeas(trial): keep=trial
print("pattern",pats[pi],"minimal obstruction size",len(keep))
for q in keep:
    print(" ",nm(q),"log pos (%.3f,%.3f)"%(L[q,0]/0.2,L[q,1]/0.2),"grid; s_c",s[q//2],"y=%.4f"%y[q], sw[q//2][:3])
ok,info=cone_lp(L[keep],y[keep],dirs,margin=True); print("t",info['t'])
